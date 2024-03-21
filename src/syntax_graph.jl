const NodeId = Int

"""
Directed graph with arbitrary attributes on nodes. Used here for representing
one or several syntax trees.
"""
struct SyntaxGraph{Attrs}
    edge_ranges::Vector{UnitRange{Int}}
    edges::Vector{NodeId}
    attributes::Attrs
end

SyntaxGraph() = SyntaxGraph{Dict{Symbol,Any}}(Vector{UnitRange{Int}}(),
                                              Vector{NodeId}(), Dict{Symbol,Any}())

# "Freeze" attribute names and types, encoding them in the type of the returned
# SyntaxGraph.
function freeze_attrs(graph::SyntaxGraph)
    frozen_attrs = (; pairs(graph.attributes)...)
    SyntaxGraph(graph.edge_ranges, graph.edges, frozen_attrs)
end

function _show_attrs(io, attributes::Dict)
    show(io, MIME("text/plain"), attributes)
end
function _show_attrs(io, attributes::NamedTuple)
    show(io, MIME("text/plain"), Dict(pairs(attributes)...))
end

function Base.show(io::IO, ::MIME"text/plain", graph::SyntaxGraph)
    print(io, typeof(graph),
          " with $(length(graph.edge_ranges)) vertices, $(length(graph.edges)) edges, and attributes:\n")
    _show_attrs(io, graph.attributes)
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

function ensure_attributes(graph::SyntaxGraph; kws...)
    g = SyntaxGraph(graph.edge_ranges, graph.edges, Dict(pairs(graph.attributes)...))
    ensure_attributes!(g; kws...)
    freeze_attrs(g)
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

function getattr(graph::SyntaxGraph{<:Dict}, name::Symbol)
    getfield(graph, :attributes)[name]
end

function getattr(graph::SyntaxGraph{<:NamedTuple}, name::Symbol)
    getfield(getfield(graph, :attributes), name)
end

function getattr(graph::SyntaxGraph, name::Symbol, default)
    get(getfield(graph, :attributes), name, default)
end

# FIXME: Probably terribly non-inferrable?
function setattr!(graph::SyntaxGraph, id; attrs...)
    for (k,v) in pairs(attrs)
        getattr(graph, k)[id] = v
    end
end

function Base.getproperty(graph::SyntaxGraph, name::Symbol)
    # FIXME: Remove access to internals
    name === :edge_ranges && return getfield(graph, :edge_ranges)
    name === :edges       && return getfield(graph, :edges)
    name === :attributes  && return getfield(graph, :attributes)
    return getattr(graph, name)
end

function _convert_nodes(graph::SyntaxGraph, node::SyntaxNode)
    id = newnode!(graph)
    graph.head[id] = head(node)
    if !isnothing(node.val)
        v = node.val
        if v isa Symbol
            setattr!(graph, id, name_val=string(v))
        else
            setattr!(graph, id, value=v)
        end
    end
    setattr!(graph, id, source=SourceRef(node.source, node.position, node.raw))
    if haschildren(node)
        cs = map(children(node)) do n
            _convert_nodes(graph, n)
        end
        setchildren!(graph, id, cs)
    end
    return id
end

#-------------------------------------------------------------------------------
struct SyntaxTree{GraphType}
    graph::GraphType
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

function Base.propertynames(tree::SyntaxTree)
    attrnames(tree)
end

function Base.get(tree::SyntaxTree, name::Symbol, default)
    attr = getattr(getfield(tree, :graph), name, nothing)
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
    SyntaxList(tree.graph, children(tree.graph, tree.id))
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

function hasattr(tree::SyntaxTree, name::Symbol)
    attr = getattr(tree.graph, name, nothing)
    return !isnothing(attr) && haskey(attr, tree.id)
end

function attrnames(tree::SyntaxTree)
    attrs = tree.graph.attributes
    [name for (name, value) in pairs(attrs) if haskey(value, tree.id)]
end

function head(tree::SyntaxTree)
    tree.head
end

# Reference to bytes within a source file
struct SourceRef
    file::SourceFile
    first_byte::Int
    # TODO: Do we need the green node, or would last_byte suffice?
    green_tree::GreenNode
end

first_byte(src::SourceRef) = src.first_byte
last_byte(src::SourceRef) = src.first_byte + span(src.green_tree) - 1
filename(src::SourceRef) = filename(src.file)
source_location(::Type{LineNumberNode}, src::SourceRef) = source_location(LineNumberNode, src.file, src.first_byte)
source_location(src::SourceRef) = source_location(src.file, src.first_byte)

function Base.show(io::IO, ::MIME"text/plain", src::SourceRef)
    highlight(io, src.file, first_byte(src):last_byte(src), note="these are the bytes you're looking for 😊", context_lines_inner=20)
end

function sourceref(tree::SyntaxTree)
    sources = tree.graph.source
    id = tree.id
    while true
        s = sources[id]
        if s isa SourceRef
            return s
        else
            id = s::NodeId
        end
    end
end

filename(tree::SyntaxTree) = return filename(sourceref(tree))
source_location(::Type{LineNumberNode}, tree::SyntaxTree) = source_location(LineNumberNode, sourceref(tree))
source_location(tree::SyntaxTree) = source_location(sourceref(tree))
first_byte(tree::SyntaxTree) = first_byte(sourceref(tree))
last_byte(tree::SyntaxTree) = last_byte(sourceref(tree))

function SyntaxTree(graph::SyntaxGraph, node::SyntaxNode)
    ensure_attributes!(graph, head=SyntaxHead, source=Union{SourceRef,NodeId},
                       value=Any, name_val=String)
    id = _convert_nodes(graph, node)
    return SyntaxTree(graph, id)
end

function SyntaxTree(node::SyntaxNode)
    return SyntaxTree(SyntaxGraph(), node)
end

attrsummary(name, value) = string(name)
attrsummary(name, value::Number) = "$name=$value"

function _value_string(ex)
    k = kind(ex)
    str = k == K"Identifier" || is_operator(k) ? ex.name_val :
          k == K"SSAValue"   ? "ssa"                 :
          k == K"core"       ? "core.$(ex.name_val)" :
          k == K"top"        ? "top.$(ex.name_val)"  :
          k == K"slot"       ? "slot" :
          repr(get(ex, :value, nothing))
    id = get(ex, :var_id, nothing)
    if !isnothing(id)
        idstr = replace(string(id),
                        "0"=>"₀", "1"=>"₁", "2"=>"₂", "3"=>"₃", "4"=>"₄",
                        "5"=>"₅", "6"=>"₆", "7"=>"₇", "8"=>"₈", "9"=>"₉")
        str = "$(str).$idstr"
    end
    if k == K"slot"
        # TODO: Ideally shouldn't need to rewrap the id here...
        srcex = SyntaxTree(ex.graph, ex.source)
        str = "$(str)/$(srcex.name_val)"
    end
    return str
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

    std_attrs = Set([:name_val,:value,:head,:source,:var_id])
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

#-------------------------------------------------------------------------------
# Lightweight vector of nodes ids with associated pointer to graph stored separately.
struct SyntaxList{GraphType, NodeIdVecType} <: AbstractVector{SyntaxTree}
    graph::GraphType
    ids::NodeIdVecType
end

function SyntaxList(graph::SyntaxGraph, ids::AbstractVector{NodeId})
    SyntaxList{typeof(graph), typeof(ids)}(graph, ids)
end

SyntaxList(graph::SyntaxGraph) = SyntaxList(graph, Vector{NodeId}())
SyntaxList(ctx) = SyntaxList(ctx.graph)

Base.size(v::SyntaxList) = size(v.ids)

Base.IndexStyle(::Type{<:SyntaxList}) = IndexLinear()

Base.getindex(v::SyntaxList, i::Int) = SyntaxTree(v.graph, v.ids[i])

function Base.setindex!(v::SyntaxList, tree::SyntaxTree, i::Int)
    v.graph === tree.graph || error("Mismatching syntax graphs")
    v.ids[i] = tree.id
end

function Base.setindex!(v::SyntaxList, id::NodeId, i::Int)
    v.ids[i] = id
end

function Base.push!(v::SyntaxList, tree::SyntaxTree)
    v.graph === tree.graph || error("Mismatching syntax graphs")
    push!(v.ids, tree.id)
end

function Base.append!(v::SyntaxList, exs)
    for e in exs
        push!(v, e)
    end
    v
end

function Base.append!(v::SyntaxList, exs::SyntaxList)
    v.graph === exs.graph || error("Mismatching syntax graphs")
    append!(v.ids, exs.ids)
    v
end

function Base.push!(v::SyntaxList, id::NodeId)
    push!(v.ids, id)
end

function Base.pop!(v::SyntaxList)
    SyntaxTree(v.graph, pop!(v.ids))
end

#-------------------------------------------------------------------------------

function build_tree(::Type{SyntaxTree}, stream::ParseStream; kws...)
    SyntaxTree(build_tree(SyntaxNode, stream; kws...))
end

