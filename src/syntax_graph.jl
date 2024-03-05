const NodeId = Int

"""
Directed graph with arbitrary attributes on nodes. Used here for representing
one or several syntax trees.
"""
struct SyntaxGraph
    edge_ranges::Vector{UnitRange{Int}}
    edges::Vector{NodeId}
    attributes::Dict{Symbol,Any}
end

SyntaxGraph() = SyntaxGraph(Vector{UnitRange{Int}}(), Vector{NodeId}(), Dict{Symbol,Any}())

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
            graph.attributes[k] = Dict{NodeId,v}()
        end
    end
end

function newnode!(graph::SyntaxGraph)
    push!(graph.edge_ranges, 0:-1) # Invalid range start => leaf node
    return length(graph.edge_ranges)
end

function setchildren!(graph::SyntaxGraph, id, children::NodeId...)
    setchildren!(graph, id, children)
end

function setchildren!(graph::SyntaxGraph, id, children)
    n = length(graph.edges)
    graph.edge_ranges[id] = n+1:(n+length(children))
    # TODO: Reuse existing edges if possible
    append!(graph.edges, children)
end

function haschildren(graph::SyntaxGraph, id)
    first(graph.edge_ranges[id]) > 0
end

function numchildren(graph::SyntaxGraph, id)
    length(graph.edge_ranges[id])
end

function children(graph::SyntaxGraph, id)
    @view graph.edges[graph.edge_ranges[id]]
end

function child(graph::SyntaxGraph, id::NodeId, i::Integer)
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
        v = node.val
        if v isa Symbol
            v = string(v)
        end
        setattr!(graph, id, value=v)
    end
    # FIXME: remove `isnothing()` check if reverting Unions in SyntaxData
    let r = node.raw
        !isnothing(r) && (setattr!(graph, id, green_tree=r))
    end
    let s = node.source
        !isnothing(s) && (setattr!(graph, id, source=s))
    end
    if haschildren(node)
        cs = map(children(node)) do n
            _convert_nodes(graph, n)
        end
        setchildren!(graph, id, cs)
    end
    return id
end

struct SyntaxTree
    graph::SyntaxGraph
    id::NodeId
end

function Base.getproperty(tree::SyntaxTree, name::Symbol)
    # FIXME: Remove access to internals
    name === :graph && return getfield(tree, :graph)
    name === :id  && return getfield(tree, :id)
    id = getfield(tree, :id)
    return get(getproperty(getfield(tree, :graph), name), id) do
        error("Property `$name[$id]` not found")
    end
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

function Base.getindex(tree::SyntaxTree, r::UnitRange)
    (child(tree, i) for i in r)
end

Base.firstindex(tree::SyntaxTree) = 1
Base.lastindex(tree::SyntaxTree) = numchildren(tree)

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

source_location(::Type{LineNumberNode}, tree::SyntaxTree) = source_location(LineNumberNode, tree.source, tree.source_pos)
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

function _value_string(ex)
    val = get(ex, :value, nothing)
    k = kind(ex)
    nodestr = k == K"Identifier" ? val :
              k == K"SSALabel" ? "#SSA-$(ex.var_id)" :
              k == K"core" ? "core.$(ex.value)" :
              repr(val)
end

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
    nodestr = haschildren(node) ? "[$(untokenize(head(node)))]" : _value_string(node)

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

function _show_syntax_tree_sexpr(io, ex)
    if !haschildren(ex)
        if is_error(ex)
            print(io, "(", untokenize(head(ex)), ")")
        else
            print(io, _value_string(ex))
        end
    else
        print(io, "(", untokenize(head(ex)))
        first = true
        for n in children(ex)
            print(io, ' ')
            _show_syntax_tree_sexpr(io, n)
            first = false
        end
        print(io, ')')
    end
end

function Base.show(io::IO, ::MIME"text/x.sexpression", node::SyntaxTree)
    _show_syntax_tree_sexpr(io, node)
end

function Base.show(io::IO, node::SyntaxTree)
    _show_syntax_tree_sexpr(io, node)
end

