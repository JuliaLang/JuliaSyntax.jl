# Experimental port of some parts of Julia's code lowering (ie, the symbolic
# non-type-related compiler passes)

TODO(msg) = throw(ErrorException("Lowering TODO: $msg"))
TODO(ex, msg) = throw(LoweringError(ex, "Lowering TODO: $msg"))

#-------------------------------------------------------------------------------
# Lowering types

"""
Unique symbolic identity for a variable within a `LoweringContext`
"""
const VarId = Int

"""
Metadata about a variable name - whether it's a local, etc
"""
struct VarInfo
    name::String
    islocal::Bool          # Local variable (if unset, variable is global)
    is_single_assign::Bool # Single assignment
    # isarg::Bool # Is a function argument ??
    # etc
end

struct SSAVar
    id::VarId
end

# Mirror of flisp scope info structure
# struct ScopeInfo
#     lambda_vars::Union{LambdaLocals,LambdaInfo}
#     parent::Union{Nothing,ScopeInfo}
#     args::Set{Symbol}
#     locals::Set{Symbol}
#     globals::Set{Symbol}
#     static_params::Set{Symbol}
#     renames::Dict{Symbol,Symbol}
#     implicit_globals::Set{Symbol}
#     warn_vars::Set{Symbol}
#     is_soft::Bool
#     is_hard::Bool
#     table::Dict{Symbol,Any}
# end

struct ScopeInfo
    locals::Dict{Symbol,VarId}
    is_soft::Bool
    is_hard::Bool
end

ScopeInfo(; is_soft=false, is_hard=false) = ScopeInfo(Dict{Symbol,VarId}(), is_soft, is_hard)

struct LoweringContext{GraphType}
    graph::GraphType
    next_var_id::Ref{VarId}
    globals::Dict{Symbol,VarId}
    scope_stack::Vector{ScopeInfo}  # Stack of name=>id mappings for each scope, innermost scope last.
    var_info::Dict{VarId,VarInfo}  # id=>info mapping containing information about all variables
end

function LoweringContext()
    graph = SyntaxGraph()
    ensure_attributes!(graph,
                       head=SyntaxHead, green_tree=GreenNode,
                       source_pos=Int, source=SourceFile,
                       value=Any,
                       scope=ScopeInfo,
                       hard_scope=Bool,
                       var_id=VarId,
                       lambda_info=LambdaInfo)
    LoweringContext(freeze_attrs(graph),
                    Ref{VarId}(1),
                    Dict{Symbol,VarId}(),
                    Vector{ScopeInfo}(),
                    Dict{VarId,VarInfo}())
end

#-------------------------------------------------------------------------------
struct LoweringError <: Exception
    ex
    msg
end

function Base.showerror(io::IO, exc::LoweringError)
    print(io, "LoweringError")
    # ctx = exc.context
    # if !isnothing(ctx)
    #     print(io, " while expanding ", ctx.macroname,
    #           " in module ", ctx.mod)
    # end
    print(io, ":\n")
    d = Diagnostic(first_byte(exc.ex), last_byte(exc.ex), error=exc.msg)
    show_diagnostic(io, d, exc.ex.source)
end

function chk_code(ex, cond)
    cond_str = string(cond)
    quote
        ex = $(esc(ex))
        @assert ex isa SyntaxTree
        try
            ok = $(esc(cond))
            if !ok
                throw(LoweringError(ex, "Expected `$($cond_str)`"))
            end
        catch
            throw(LoweringError(ex, "Structure error evaluating `$($cond_str)`"))
        end
    end
end

# Check a condition involving an expression, throwing a LoweringError if it
# doesn't evaluate to true. Does some very simple pattern matching to attempt
# to extract the expression variable from the left hand side.
macro chk(cond)
    ex = cond
    while true
        if ex isa Symbol
            break
        elseif ex.head == :call
            ex = ex.args[2]
        elseif ex.head == :ref
            ex = ex.args[1]
        elseif ex.head == :.
            ex = ex.args[1]
        elseif ex.head in (:(==), :(in), :<, :>)
            ex = ex.args[1]
        else
            error("Can't analyze $cond")
        end
    end
    chk_code(ex, cond)
end

macro chk(ex, cond)
    chk_code(ex, cond)
end

#-------------------------------------------------------------------------------

# pass 1: syntax desugaring

function is_quoted(ex)
    kind(ex) in KSet"quote top core globalref outerref break inert
                     meta inbounds inline noinline loopinfo"
end

function expand_condition(ctx, ex)
    if head(ex) == K"block" || head(ex) == K"||" || head(ex) == K"&&"
        # || and && get special lowering so that they compile directly to jumps
        # rather than first computing a bool and then jumping.
        error("TODO expand_condition")
    end
    expand_forms(ctx, ex)
end

function expand_forms(ctx, ex)
    ensure_attributes!(ctx.graph,
                       scope=ScopeInfo,
                       hard_scope=Bool,
                       var_id=VarId,
                       lambda_info=LambdaInfo)
    SyntaxTree(ctx.graph, _expand_forms(ctx, ex))
end

_node_id(ex::NodeId) = ex
_node_id(ex::SyntaxTree) = ex.id

_node_ids() = ()
_node_ids(c, cs...) = (_node_id(c), _node_ids(cs...)...)

function makenode(ctx::LoweringContext, srcref, head, children...; attrs...)
    makenode(ctx.graph, srcref, head, _node_ids(children...)...; attrs...)
end

function makenode(graph::SyntaxGraph, srcref, head, children...; attrs...)
    id = newnode!(graph)
    if kind(head) in (K"Identifier", K"core", K"SSALabel") || is_literal(head)
        @assert length(children) == 0
    else
        setchildren!(graph, id, children)
    end
    setattr!(graph, id; head=head, attrs...)
    if srcref isa NodeId
        # Hack!
        srcref = SyntaxTree(graph, srcref)
    end
    setattr!(graph, id;
             source=srcref.source,
             green_tree=srcref.green_tree,
             source_pos=srcref.source_pos)
    return id
end

function ssavar(ctx::LoweringContext, srcref)
    id = makenode(ctx, srcref, K"SSALabel", var_id=ctx.next_var_id[])
    ctx.next_var_id[] += 1
    return id
end

function assign_tmp(ctx::LoweringContext, ex)
    tmp = ssavar(ctx, ex)
    tmpdef = makenode(ctx, ex, K"=", tmp, ex)
    tmp, tmpdef
end

function expand_assignment(ctx, ex)
end

function is_sym_decl(x)
    k = kind(x)
    k == K"Identifier" || k == K"::"
end

# Identifier made of underscores
function is_placeholder(ex)
    kind(ex) == K"Identifier" && all(==('_'), ex.value::String)
end

function decl_var(ex)
    kind(ex) == K"::" ? ex[1] : ex
end

function expand_let(ctx, ex)
    is_hard_scope = get(ex, :hard_scope, true)
    blk = expand_forms(ctx, ex[2])
    for binding in Iterators.reverse(children(ex[1]))
        kb = kind(binding)
        if is_sym_decl(kb)
            blk = makenode(ctx, ex, K"block",
                makenode(ctx, ex, K"local", binding; sr...),
                blk;
                sr...,
                scope=ScopeInfo(is_hard=is_hard_scope)
            )
        elseif kb == K"=" && numchildren(binding) == 2
            lhs = binding[1]
            rhs = binding[2]
            if is_sym_decl(lhs)
                tmp, tmpdef = assign_tmp(ctx, rhs)
                blk = makenode(ctx, binding, K"block",
                    tmpdef,
                    makenode(ctx, ex, K"block",
                        makenode(ctx, lhs, K"local_def", lhs), # TODO: Use K"local" with attr?
                        makenode(ctx, rhs, K"=", decl_var(lhs), tmp),
                        blk;
                        scope=ScopeInfo(is_hard=is_hard_scope)
                    )
                )
            else
                TODO("Functions and multiple assignment")
            end
        else
            throw(LoweringError(binding, "Invalid binding in let"))
            continue
        end
    end
    return blk
end

# FIXME: The problem of "what is an identifier" pervades lowering ... we have
# various things which seem like identifiers:
#
# * Identifier (symbol)
# * K"var" nodes
# * Operator kinds
# * Underscore placeholders
#
# Can we avoid having the logic of "what is an identifier" repeated by dealing
# with these during desugaring
# * Attach an identifier attribute to nodes. If they're an identifier they get this
# * Replace operator kinds by K"Identifier" in parsing?
# * Replace operator kinds by K"Identifier" in desugaring?
function identifier_name(ex)
    kind(ex) == K"var" ? ex[1] : ex
end

function analyze_function_arg(full_ex)
    name = nothing
    type = nothing
    default = nothing
    is_slurp = false
    is_nospecialize = false
    ex = full_ex
    while true
        k = kind(ex)
        if k == K"Identifier" || k == K"tuple"
            name = ex
            break
        elseif k == K"::"
            @chk numchildren(ex) in (1,2)
            if numchildren(ex) == 1
                type = ex[1]
            else
                name = ex[1]
                type = ex[2]
            end
            break
        elseif k == K"..."
            @chk full_ex !is_slurp
            @chk numchildren(ex) == 1
            is_slurp = true
            ex = ex[1]
        elseif k == K"meta"
            @chk ex[1].value == "nospecialize"
            is_nospecialize = true
            ex = ex[2]
        elseif k == K"="
            @chk full_ex isnothing(default) && !is_slurp
            default = ex[2]
            ex = ex[1]
        else
            throw(LoweringError(ex, "Invalid function argument"))
        end
    end
    return (name=name,
            type=type,
            default=default,
            is_slurp=is_slurp,
            is_nospecialize=is_nospecialize)
end

core_ref(ctx, ex, name) = makenode(ctx, ex, K"core", value=name)
Any_type(ctx, ex) = core_ref(ctx, ex, "Any")
svec_type(ctx, ex) = core_ref(ctx, ex, "svec")
nothing_(ctx, ex) = core_ref(ctx, ex, "nothing")
unused(ctx, ex) = core_ref(ctx, ex, "UNUSED")

function expand_function_def(ctx, ex)
    @chk numchildren(ex) in (1,2)
    name = ex[1]
    if kind(name) == K"where"
        TODO("where handling")
    end
    return_type = nothing
    if kind(name) == K"::"
        @chk numchildren(name) == 2
        return_type = name[2]
        name = name[1]
    end
    if numchildren(ex) == 1 && is_identifier(name) # TODO: Or name as globalref
        if !is_valid_name(name)
            throw(LoweringError(name, "Invalid function name"))
        end
        return makenode(ctx, ex, K"method", identifier_name(name))
    elseif kind(name) == K"call"
        callex = name
        body = ex[2]
        # TODO
        # static params
        # nospecialize
        # argument destructuring
        # dotop names
        # overlays

        # Add self argument where necessary
        args = name[2:end]
        name = name[1]
        if kind(name) == K"::"
            if numchildren(name) == 1
                farg = makenode(ctx, name, K"::",
                                makenode(ctx, name, K"Identifier", value="#self#"),
                                name[1])
            else
                TODO("Fixme type")
                farg = name
            end
            function_name = nothing_(ctx, ex)
        else
            if !is_valid_name(name)
                throw(LoweringError(name, "Invalid function name"))
            end
            farg = makenode(ctx, name, K"::",
                            makenode(ctx, name, K"Identifier", value="#self#"),
                            makenode(ctx, name, K"call",
                                     makenode(ctx, name, K"core", value="Typeof"),
                                     name))
            function_name = name
        end

        # preamble is arbitrary code which computes
        # svec(types, sparms, location)

        arg_names = []
        arg_types = []
        for (i,arg) in enumerate(args)
            info = analyze_function_arg(arg)
            aname = (isnothing(info.name) || is_placeholder(info.name)) ?
                    unused(ctx, arg) : info.name
            push!(arg_names, aname)
            atype = !isnothing(info.type) ? info.type : Any_type(ctx, arg)
            @assert !info.is_nospecialize # TODO
            @assert !isnothing(info.name) && kind(info.name) == K"Identifier" # TODO
            if info.is_slurp
                if i != length(args)
                    throw(LoweringError(arg, "`...` may only be used for the last function argument"))
                end
                atype = makenode(K"curly", core_ref(ctx, arg, "Vararg"), arg)
            end
            push!(arg_types, atype)
        end

        preamble = makenode(ctx, ex, K"call",
                            svec_type(ctx, callex),
                            makenode(ctx, callex, K"call",
                                     svec_type(ctx, name),
                                     arg_types...),
                            makenode(ctx, callex, K"Value", value=source_location(LineNumberNode, callex))
                           )
        if !isnothing(return_type)
            ret_var, ret_assign = assign_tmp(ctx, return_type)
            body = makenode(ctx, body, K"block",
                            ret_assign,
                            body,
                            scope=ScopeInfo())
        else
            ret_var = nothing
            body = makenode(ctx, body, K"block",
                            body,
                            scope=ScopeInfo())
        end
        lambda = makenode(ctx, body, K"lambda", body;
                          lambda_info=LambdaInfo(arg_names, ret_var))
        return makenode(ctx, ex, K"method",
                        function_name,
                        preamble,
                        lambda)
    elseif kind(name) == K"tuple"
        TODO(name, "Anon function lowering")
    else
        throw(LoweringError(name, "Bad function definition"))
    end
end

function _expand_forms(ctx, ex)
    k = kind(ex)
    if k == K"function"
        expand_function_def(ctx, ex)
    elseif k == K"let"
        return expand_let(ctx, ex)
    elseif is_operator(k) && !haschildren(ex)
        return makenode(ctx, ex, K"Identifier", value=ex.value)
    elseif k == K"char" || k == K"var"
        @assert numchildren(ex) == 1
        return ex[1]
    elseif k == K"string" && numchildren(ex) == 1 && kind(ex[1]) == K"String"
        return ex[1]
    elseif !haschildren(ex)
        return ex
    else
        if k == K"="
            @chk numchildren(ex) == 2
            if kind(ex[1]) != K"Identifier"
                TODO(ex, "destructuring assignment")
            end
        end
        # FIXME: What to do about the ids vs SyntaxTree?
        makenode(ctx, ex, head(ex), [_expand_forms(ctx,e) for e in children(ex)]...)
    end
end

#-------------------------------------------------------------------------------
# Pass 2: analyze scopes (passes 2/3 in flisp code)
#
# This pass analyzes the names (variables/constants etc) used in scopes
#
# This pass records information about variables used by closure conversion.
# finds which variables are assigned or captured, and records variable
# type declarations.
#
# This info is recorded by setting the second argument of `lambda` expressions
# in-place to
#   (var-info-lst captured-var-infos ssavalues static_params)
# where var-info-lst is a list of var-info records

function is_underscore(ex)
    k = kind(ex)
    return (k == K"Identifier" && valueof(ex) == :_) ||
           (k == K"var" && valueof(ex[1]) == :_)
end

function identifier_name_str(ex)
    identifier_name(ex).value
end

function is_valid_name(ex)
    n = identifier_name_str(ex)
    n !== "ccall" && n !== "cglobal"
end

function _schedule_traverse(stack, e)
    push!(stack, e)
    return nothing
end
function _schedule_traverse(stack, es::Union{Tuple,Vector,Base.Generator})
    append!(stack, es)
    return nothing
end

function traverse_ast(f, ex)
    todo = [ex]
    while !isempty(todo)
        e1 = pop!(todo)
        f(e1, e->_schedule_traverse(todo, e))
    end
end

function find_in_ast(f, ex)
    todo = [ex]
    while !isempty(todo)
        e1 = pop!(todo)
        res = f(e1, e->_schedule_traverse(todo, e))
        if !isnothing(res)
            return res
        end
    end
    return nothing
end

# NB: This only really works after expand_forms has already processed assignments.
function find_assigned_vars(ex)
    vars = Vector{typeof(ex)}()
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == K"method"
            TODO(e, "method")
            return nothing
        elseif k == K"="
            v = decl_var(e[1])
            if !(kind(v) in KSet"SSALabel globalref outerref" || is_underscore(e))
                push!(vars, v)
            end
            traverse(e[2])
        else
            traverse(children(e))
        end
    end
    var_names = String[v.value for v in vars]
    return unique(var_names)
end

function find_decls(decl_kind, ex)
    vars = Vector{typeof(ex)}()
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == decl_kind
            if !is_underscore(e[1])
                push!(vars, decl_var(e[1]))
            end
        else
            traverse(children(e))
        end
    end
    var_names = String[v.value for v in vars]
    return unique(var_names)
end

# Determine whether decl_kind is in the scope of `ex`
#
# flisp: find-scope-decl
function has_scope_decl(decl_kind, ex)
    find_in_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == decl_kind
            return e
        else
            traverse(children(ex))
        end
    end
end

# TODO:
# Incorporate hygenic-scope here so we always have a parent scope when
# processing variables

# Steps
# 1. Deal with implicit locals and globals only
# 2. Add local, global etc later

# struct LambdaVars
#     # For analyze-variables pass
#     # var_info_lst::Set{Tuple{Symbol,Symbol}} # ish?
#     # captured_var_infos ??
#     # ssalabels::Set{SSALabel}
#     # static_params::Set{Symbol}
# end

struct LambdaInfo
    arg_names::Vector{NodeId}
    return_type::Union{Nothing,NodeId}
    arg_vars::Set{VarId}
    body_vars::Set{VarId}
end

function LambdaInfo(args, return_type)
    LambdaInfo([_node_id(a) for a in args],
               isnothing(return_type) ? nothing : _node_id(return_type),
               Set{VarId}(),
               Set{VarId}())
end

function resolve_scopes(ctx, ex)
    thk_vars = LambdaInfo()
    resolve_scopes(ctx, thk_vars, ex)
end

function resolve_scopes(ctx, lambda_vars, ex)
    k = kind(ex)
    if k == K"Identifier"
        # Look up identifier
        name = ex.value
        for s in Iterators.reverse(ctx.scope_stack)
        end
    elseif k == K"global"
        TODO("global")
    elseif k == K"local" || k == K"local_def"
        TODO("local") # Remove these
    # TODO
    # elseif require_existing_local
    # elseif locals # return Dict of locals
    # elseif islocal
    elseif k == K"lambda"
        vars = LambdaInfo(ex[1])
        resolve_scopes(ctx, vars, ex[2])
    elseif hasattr(ex, :scope)
        # scope-block
    end
    # scope = get(ex, :scope, nothing)
    # if !isnothing(scope)
    # for e in children(ex)
    #     resolve_scopes(ctx, child_scope, e)
    # end
end

#-------------------------------------------------------------------------------
# Pass 3: closure conversion
#
# This pass lifts all inner functions to the top level by generating
# a type for them.
#
# For example `f(x) = y->(y+x)` is converted to
#
#     immutable yt{T}
#         x::T
#     end
#
#     (self::yt)(y) = y + self.x
#
#     f(x) = yt(x)

#-------------------------------------------------------------------------------
# Main entry points

# Passes 1-3
# function symbolic_simplify()
# end

# Passes 1-4
# TODO: What's a good name for this? It contains
# * Symbolic simplification
# * Tree flattening / conversion to linear IR
function lower_code(ex)
end
