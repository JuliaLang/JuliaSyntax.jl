# Experimental port of some parts of Julia's code lowering (ie, the symbolic
# non-type-related compiler passes)

TODO(msg) = throw(ErrorException("Lowering TODO: $msg"))
TODO(ex, msg) = throw(LoweringError(ex, "Lowering TODO: $msg"))

#-------------------------------------------------------------------------------
# Lowering types

"""
Unique symbolic identity for a variable within a `DesugaringContext`
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

struct LambdaInfo
    # TODO: Make this concretely typed
    args::SyntaxList
    ret_var::Union{Nothing,SyntaxTree}
end

abstract type AbstractLoweringContext end

struct DesugaringContext{GraphType} <: AbstractLoweringContext
    graph::GraphType
    next_var_id::Ref{VarId}
end

function DesugaringContext()
    graph = SyntaxGraph()
    ensure_attributes!(graph,
                       head=SyntaxHead, green_tree=GreenNode,
                       source_pos=Int, source=SourceFile,
                       value=Any, name_val=String,
                       scope_type=Symbol, # :hard or :soft
                       var_id=VarId,
                       lambda_info=LambdaInfo)
    DesugaringContext(freeze_attrs(graph),
                    Ref{VarId}(1))
end

#-------------------------------------------------------------------------------
# Error handling

# Errors found during lowering will result in LoweringError being thrown to
# indicate the syntax causing the error.
struct LoweringError <: Exception
    ex::SyntaxTree
    msg::String
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

function _chk_code(ex, cond)
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

# Internal error checking macro.
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
    _chk_code(ex, cond)
end

macro chk(ex, cond)
    _chk_code(ex, cond)
end

#-------------------------------------------------------------------------------
# AST creation utilities
_node_id(ex::NodeId) = ex
_node_id(ex::SyntaxTree) = ex.id

_node_ids() = ()
_node_ids(c, cs...) = (_node_id(c), _node_ids(cs...)...)

function _makenode(graph::SyntaxGraph, srcref, head, children; attrs...)
    id = newnode!(graph)
    if kind(head) in (K"Identifier", K"core", K"top", K"SSAValue", K"Value") || is_literal(head)
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
    return SyntaxTree(graph, id)
end

function makenode(graph::SyntaxGraph, srcref, head, children...; attrs...)
    _makenode(graph, srcref, head, children; attrs...)
end

function makenode(ctx::AbstractLoweringContext, srcref, head, children::SyntaxTree...; attrs...)
    _makenode(ctx.graph, srcref, head, _node_ids(children...); attrs...)
end

function makenode(ctx::AbstractLoweringContext, srcref, head, children::SyntaxList; attrs...)
    ctx.graph === children.graph || error("Mismatching graphs")
    _makenode(ctx.graph, srcref, head, children.ids; attrs...)
end

function mapchildren(f, ctx, ex)
    cs = SyntaxList(ctx)
    for e in children(ex)
        push!(cs, f(e))
    end
    ex2 = makenode(ctx, ex, head(ex), cs)
    # Copy all attributes.
    # TODO: Make this type stable and efficient
    for v in values(ex.graph.attributes)
        if haskey(v, ex.id)
            v[ex2.id] = v[ex.id]
        end
    end
    return ex2
end

function new_var_id(ctx::AbstractLoweringContext)
    id = ctx.next_var_id[]
    ctx.next_var_id[] += 1
    return id
end

# Create a new SSA variable
function ssavar(ctx::AbstractLoweringContext, srcref)
    id = makenode(ctx, srcref, K"SSAValue", var_id=new_var_id(ctx))
    return id
end

# Assign `ex` to an SSA variable.
# Return (variable, assignment_node)
function assign_tmp(ctx::AbstractLoweringContext, ex)
    var = ssavar(ctx, ex)
    assign_var = makenode(ctx, ex, K"=", var, ex)
    var, assign_var
end

# Convenience functions to create leaf nodes referring to identifiers within
# the Core and Top modules.
core_ref(ctx, ex, name) = makenode(ctx, ex, K"core", name_val=name)
Any_type(ctx, ex) = core_ref(ctx, ex, "Any")
svec_type(ctx, ex) = core_ref(ctx, ex, "svec")
nothing_(ctx, ex) = core_ref(ctx, ex, "nothing")
unused(ctx, ex) = core_ref(ctx, ex, "UNUSED")

top_ref(ctx, ex, name) = makenode(ctx, ex, K"top", name_val=name)

#-------------------------------------------------------------------------------
# Predicates and accessors working on expression trees

function is_quoted(ex)
    kind(ex) in KSet"quote top core globalref outerref break inert
                     meta inbounds inline noinline loopinfo"
end

function is_sym_decl(x)
    k = kind(x)
    k == K"Identifier" || k == K"::"
end

# Identifier made of underscores
function is_placeholder(ex)
    kind(ex) == K"Identifier" && all(==('_'), ex.name_val)
end

function identifier_name(ex)
    kind(ex) == K"var" ? ex[1] : ex
end

function is_valid_name(ex)
    n = identifier_name(ex).name_val
    n !== "ccall" && n !== "cglobal"
end

function decl_var(ex)
    kind(ex) == K"::" ? ex[1] : ex
end


#-------------------------------------------------------------------------------
# Lowering Pass 1 - basic desugaring
function expand_condition(ctx, ex)
    if head(ex) == K"block" || head(ex) == K"||" || head(ex) == K"&&"
        # || and && get special lowering so that they compile directly to jumps
        # rather than first computing a bool and then jumping.
        error("TODO expand_condition")
    end
    expand_forms(ctx, ex)
end

function expand_assignment(ctx, ex)
end

function expand_let(ctx, ex)
    scope_type = get(ex, :scope_type, :hard)
    blk = ex[2]
    for binding in Iterators.reverse(children(ex[1]))
        kb = kind(binding)
        if is_sym_decl(kb)
            blk = makenode(ctx, ex, K"block",
                makenode(ctx, ex, K"local", binding; sr...),
                blk;
                sr...,
                scope_block_type=(is_hard ? :hard : :soft)
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
                        scope_type=scope_type
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

function expand_call(ctx, ex)
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
            @chk ex[1].name_val == "nospecialize"
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
                            scope_type=:hard)
        else
            ret_var = nothing
            body = makenode(ctx, body, K"block",
                            body,
                            scope_type=:hard)
        end
        lambda = makenode(ctx, body, K"lambda", body,
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

function expand_forms(ctx::DesugaringContext, ex::SyntaxTree)
    k = kind(ex)
    # if k == K"call"
    #     expand_call(ctx, ex)
    if k == K"function"
        expand_forms(ctx, expand_function_def(ctx, ex))
    elseif k == K"let"
        return expand_forms(ctx, expand_let(ctx, ex))
    elseif is_operator(k) && !haschildren(ex)
        return makenode(ctx, ex, K"Identifier", value=ex.name_val)
    elseif k == K"char" || k == K"var"
        @chk numchildren(ex) == 1
        return ex[1]
    elseif k == K"string"
        if numchildren(ex) == 1 && kind(ex[1]) == K"String"
            return ex[1]
        else
            expand_forms(ctx,
                makenode(ctx, ex, K"call", top_ref(ctx, ex, "string"), children(ex)...))
        end
    elseif k == K"tuple"
        # TODO: named tuples
        expand_forms(ctx, makenode(ctx, ex, K"call", core_ref(ctx, ex, "tuple"), children(ex)...))
    elseif !haschildren(ex)
        return ex
    else
        if k == K"="
            @chk numchildren(ex) == 2
            if kind(ex[1]) ∉ (K"Identifier", K"SSAValue")
                TODO(ex, "destructuring assignment")
            end
        end
        mapchildren(e->expand_forms(ctx,e), ctx, ex)
    end
end

