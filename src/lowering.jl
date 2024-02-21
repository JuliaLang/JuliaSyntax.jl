# Experimental port of some parts of Julia's code lowering (ie, the symbolic
# non-type-related compiler passes)

#-------------------------------------------------------------------------------
"""
Directed graph with arbitrary attributes on nodes. Used here for representing
one or several syntax trees.
"""
struct SyntaxGraph
    edge_ranges::Vector{UnitRange{Int}}
    edges::Vector{Int}
    attributes::Dict{Symbol,Any}
end

SyntaxGraph() = SyntaxGraph(Vector{UnitRange{Int}}(), Vector{Int}(), Dict{Symbol,Any}())

function Base.show(io::IO, ::MIME"text/plain", graph::SyntaxGraph)
    print(io, SyntaxGraph,
          " with $(length(graph.edge_ranges)) vertices, $(length(graph.edges)) edges, and attributes:\n")
    show(io, MIME("text/plain"), graph.attributes)
end

function ensure_attributes!(graph::SyntaxGraph; kws...)
    for (k,v) in pairs(kws)
        @assert k isa Symbol
        @assert v isa Type
        if haskey(graph.attributes, k)
            v0 = valtype(graph.attributes[k])
            v == v0 || throw(ErrorException("Attribute type mismatch $v != $v0"))
        else
            graph.attributes[k] = Dict{Int,v}()
        end
    end
end

function newnode!(graph::SyntaxGraph)
    push!(graph.edge_ranges, 1:0)
    return length(graph.edge_ranges)
end

function setchildren!(graph::SyntaxGraph, id, children::Integer...)
    setchildren!(graph, id, children)
end

function setchildren!(graph::SyntaxGraph, id, children)
    n = length(graph.edges)
    graph.edge_ranges[id] = n+1:(n+length(children))
    # TODO: Reuse existing edges if possible
    append!(graph.edges, children)
end

function haschildren(graph::SyntaxGraph, id)
    length(graph.edge_ranges[id]) > 0
end

function numchildren(graph::SyntaxGraph, id)
    length(graph.edge_ranges[id])
end

function children(graph::SyntaxGraph, id)
    @view graph.edges[graph.edge_ranges[id]]
end

function child(graph::SyntaxGraph, id::Int, i::Integer)
    graph.edges[graph.edge_ranges[id][i]]
end

# FIXME: Probably terribly non-inferrable?
function setattr!(graph::SyntaxGraph, id; attrs...)
    for (k,v) in pairs(attrs)
        graph.attributes[k][id] = v
    end
end

function Base.getproperty(graph::SyntaxGraph, name::Symbol)
    # FIXME: Remove access to internals
    name === :edge_ranges && return getfield(graph, :edge_ranges)
    name === :edges       && return getfield(graph, :edges)
    name === :attributes  && return getfield(graph, :attributes)
    return getfield(graph, :attributes)[name]
end

function Base.get(graph::SyntaxGraph, name::Symbol, default)
    get(getfield(graph, :attributes), name, default)
end

function _convert_nodes(graph::SyntaxGraph, node::SyntaxNode)
    id = newnode!(graph)
    graph.head[id] = head(node)
    # FIXME: Decide on API here which isn't terribly inefficient
    graph.source_pos[id] = node.position
    # setattr!(graph, id, source_pos=node.position)
    if !isnothing(node.val)
        setattr!(graph, id, value=node.val)
    end
    # FIXME: remove `isnothing()` check if reverting Unions in SyntaxData
    let r = node.raw
        !isnothing(r) && (setattr!(graph, id, green_tree=r))
    end
    let s = node.source
        !isnothing(s) && (setattr!(graph, id, source=s))
    end
    cs = map(children(node)) do n
        _convert_nodes(graph, n)
    end
    setchildren!(graph, id, cs)
    return id
end

struct SyntaxTree
    graph::SyntaxGraph
    id::Int
end

function Base.getproperty(tree::SyntaxTree, name::Symbol)
    # FIXME: Remove access to internals
    name === :graph && return getfield(tree, :graph)
    name === :id  && return getfield(tree, :id)
    return getproperty(getfield(tree, :graph), name)[getfield(tree, :id)]
end

function Base.get(tree::SyntaxTree, name::Symbol, default)
    attr = get(getfield(tree, :graph), name, nothing)
    return isnothing(attr) ? default :
           get(attr, getfield(tree, :id), default)
end

function haschildren(tree::SyntaxTree)
    haschildren(tree.graph, tree.id)
end

function numchildren(tree::SyntaxTree)
    numchildren(tree.graph, tree.id)
end

function children(tree::SyntaxTree)
    (SyntaxTree(tree.graph, c) for c in children(tree.graph, tree.id))
end

function child(tree::SyntaxTree, i::Integer)
    SyntaxTree(tree.graph, child(tree.graph, tree.id, i))
end

function Base.getindex(tree::SyntaxTree, i::Integer)
    child(tree, i)
end

function filename(tree::SyntaxTree)
    return filename(tree.source)
end

function hasattr(tree::SyntaxTree, name::Symbol)
    attr = get(tree.graph.attributes, name, nothing)
    return !isnothing(attr) && haskey(attr, tree.id)
end

function attrnames(tree::SyntaxTree)
    attrs = tree.graph.attributes
    [name for (name, value) in attrs if haskey(value, tree.id)]
end

source_location(tree::SyntaxTree) = source_location(tree.source, tree.source_pos)
first_byte(tree::SyntaxTree) = tree.source_pos
last_byte(tree::SyntaxTree) = tree.source_pos + span(tree.green_tree) - 1

function head(tree::SyntaxTree)
    tree.head
end

function SyntaxTree(graph::SyntaxGraph, node::SyntaxNode)
    ensure_attributes!(graph, head=SyntaxHead, green_tree=GreenNode,
                       source_pos=Int, source=SourceFile, value=Any)
    id = _convert_nodes(graph, node)
    return SyntaxTree(graph, id)
end

function SyntaxTree(node::SyntaxNode)
    return SyntaxTree(SyntaxGraph(), node)
end

attrsummary(name, value) = string(name)
attrsummary(name, value::Number) = "$name=$value"

function _show_syntax_tree(io, current_filename, node, indent, show_byte_offsets)
    if hasattr(node, :source)
        fname = filename(node)
        line, col = source_location(node)
        posstr = "$(lpad(line, 4)):$(rpad(col,3))"
        if show_byte_offsets
            posstr *= "│$(lpad(first_byte(node),6)):$(rpad(last_byte(node),6))"
        end
    else
        fname = nothing
        posstr = "        "
        if show_byte_offsets
            posstr *= "│             "
        end
    end
    val = get(node, :value, nothing)
    nodestr = haschildren(node) ? "[$(untokenize(head(node)))]" :
              isa(val, Symbol) ? string(val) :
              kind(node) == K"SSALabel" ? "#SSA-$(node.var_id)" :
              repr(val)

    treestr = string(indent, nodestr)

    std_attrs = Set([:value,:source_pos,:head,:source,:green_tree])
    attrstr = join([attrsummary(n, getproperty(node, n)) for n in attrnames(node) if n ∉ std_attrs], ",")
    if !isempty(attrstr)
        treestr = string(rpad(treestr, 40), "│ $attrstr")
    end

    # Add filename if it's changed from the previous node
    if fname != current_filename[] && !isnothing(fname)
        #println(io, "# ", fname)
        treestr = string(rpad(treestr, 80), "│$fname")
        current_filename[] = fname
    end
    println(io, posstr, "│", treestr)
    if haschildren(node)
        new_indent = indent*"  "
        for n in children(node)
            _show_syntax_tree(io, current_filename, n, new_indent, show_byte_offsets)
        end
    end
end

function Base.show(io::IO, ::MIME"text/plain", tree::SyntaxTree; show_byte_offsets=false)
    println(io, "line:col│ tree                                   │ attributes                            | file_name")
    _show_syntax_tree(io, Ref{Union{Nothing,String}}(nothing), tree, "", show_byte_offsets)
end


#-------------------------------------------------------------------------------
# Utilities

"""
Unique symbolic identity for a variable within a `LoweringContext`
"""
const VarId = Int

"""
Metadata about a variable name - whether it's a local, etc
"""
struct VarInfo
    islocal::Bool # Local variable (if unset, variable is global)
    # isarg::Bool # Is a function argument ??
    # etc
end

struct SSAVar
    id::VarId
end

struct LoweringContext
    graph::SyntaxGraph
    next_var_id::Ref{VarId}
    scope_stack::Vector{Dict{String,VarId}}  # Stack of name=>id mappings for each scope, innermost scope last.
    var_info::Dict{VarId,VarInfo}
    diagnostics::Vector{Diagnostic}
end

function LoweringContext()
    LoweringContext(SyntaxGraph(),
                    Ref{VarId}(1),
                    Vector{Dict{String,VarId}}(),
                    Dict{VarId,VarInfo}(),
                    Vector{Diagnostic}())
end

function emit_error(ctx::LoweringContext, ex, kws...)
    emit_error(ctx.diagnostics, first_byte(ex):last_byte(ex), kws...)
end

function SSALabel(ctx, srcref)
    val = ctx.next_var_id[]
    ctx.next_var_id[] += 1
    SyntaxNode(K"SSALabel", val, srcref=srcref)
end

function Identifier(val, srcref)
    SyntaxNode(K"Identifier", val, srcref=srcref)
end

newnode!(ctx::LoweringContext) = newnode!(ctx.graph)
setchildren!(ctx::LoweringContext, args...) = setchildren!(ctx.graph, args...)

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

function blockify(ex)
    kind(ex) == K"block" ? ex : SyntaxNode(K"block", ex, [ex])
end

function expand_forms(ctx, ex)
    ensure_attributes!(ctx.graph, scope=ScopeInfo)
    ensure_attributes!(ctx.graph, hard_scope=Bool)
    ensure_attributes!(ctx.graph, var_id=VarId)
    SyntaxTree(ctx.graph, _expand_forms(ctx, ex))
end

_children_ids() = ()
_children_ids(c::Integer, cs...) = (Int(c), _children_ids(cs...)...)
_children_ids(c::SyntaxTree, cs...) = (c.id, _children_ids(cs...)...)

function makenode(ctx::LoweringContext, srcref, head, children...; attrs...)
    makenode(ctx.graph, srcref, head, _children_ids(children...)...; attrs...)
end

function makenode(graph::SyntaxGraph, srcref, head, children...; attrs...)
    id = newnode!(graph)
    setchildren!(graph, id, children)
    setattr!(graph, id; head=head, attrs...)
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

function decl_var(ex)
    kind(ex) == K"::" ? ex[1] : ex
end

function expand_let(ctx, ex)
    is_hard_scope = get(ex, :hard_scope, true)
    blk = ex[2].id
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
            emit_error(ctx, binding, error="Invalid binding in let")
            continue
        end
    end
    return blk
end

function _expand_forms(ctx, ex)
    k = kind(ex)
    if k == K"while"
        # SyntaxNode(K"break_block", ex, [
        #     Identifier(:loop_exit, ex), # Should this refer syntactically to the `end`?
        #     SyntaxNode(K"_while", ex, [
        #         expand_condition(ctx, ex[1]),
        #         SyntaxNode(K"break_block", ex, [
        #             Identifier(:loop_cont, ex[2]),
        #             SyntaxNode(K"scope_block", ex[2], [
        #                 blockify(_expand_forms(ctx, ex[2]))
        #             ])
        #         ])
        #     ])
        # ])
    elseif k == K"let"
        return expand_let(ctx, ex)
    elseif !haschildren(ex)
        return ex
    else
        if k == K"=" && (numchildren(ex) != 2 && kind(ex[1]) != K"Identifier")
            error("TODO")
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

function decl_var(ex)
    kind(ex) == K"::" ? ex[1] : ex
end

function is_underscore(ex)
    k = kind(ex)
    return (k == K"Identifier" && valueof(ex) == :_) ||
           (k == K"var" && valueof(ex[1]) == :_)
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
    if kind(ex) == K"var"
        ex = ex[1]
    end
    valueof(ex)
end

function is_valid_name(ex)
    n = identifier_name(ex)
    n !== :ccall && n !== :cglobal
end

function _schedule_traverse(stack, e::SyntaxNode)
    push!(stack, e)
    return nothing
end
function _schedule_traverse(stack, es::Union{Tuple,Vector})
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
    vars = SyntaxNode[]
    # _find_assigned_vars(vars, ex)
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == K"method"
            error("TODO")
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
    return unique(vars)
end

function find_decls(decl_kind, ex)
    vars = SyntaxNode[]
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

struct LambdaLocals
    # For resolve-scopes pass
    locals::Set{Symbol}
end

struct LambdaVars
    # For analyze-variables pass
    # var_info_lst::Set{Tuple{Symbol,Symbol}} # ish?
    # captured_var_infos ??
    # ssalabels::Set{SSALabel}
    # static_params::Set{Symbol}
end

# TODO:
# 1. Use `.val` to store LambdaVars/LambdaLocals/ScopeInfo
# 2. Incorporate hygenic-scope here so we always have a parent scope when
#    processing variables rather than putting them into a thunk (??)

# Mirror of flisp scope info structure
# struct ScopeInfo
#     lambda_vars::Union{LambdaLocals,LambdaVars}
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
    locals::Set{Symbol}
    is_soft::Bool
    is_hard::Bool
end

ScopeInfo(; is_soft=false, is_hard=false) = ScopeInfo(Set{Symbol}(), is_soft, is_hard)

# Transform lambdas from
#   (lambda (args ...) body)
# to the form
#   (lambda (args...) (locals...) body)
function resolve_scopes_(ctx, scope, ex)
end

function resolve_scopes(ctx, ex)
    resolve_scopes_(ctx, scope, ex)
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
# Pass 4: Flatten to linear IR


