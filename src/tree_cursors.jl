using Base.Iterators: Reverse

"""
    GreenTreeCursor

Represents a cursors into a ParseStream output buffer that makes it easy to
work with the green tree representation.
"""
struct GreenTreeCursor
    parser_output::Vector{RawGreenNode}
    position::UInt32
end
GreenTreeCursor(stream::ParseStream) = GreenTreeCursor(stream.output, length(stream.output))

this(node::GreenTreeCursor) = node.parser_output[node.position]

# Debug printing
function Base.show(io::IO, node::GreenTreeCursor)
    print(io, Base.summary(this(node)), " @", node.position)
end

# Reverse iterator interface
Base.reverse(node::GreenTreeCursor) = Base.Iterators.Reverse(node)
Base.IteratorSize(::Type{Reverse{GreenTreeCursor}}) = Base.SizeUnknown()
@inline function Base.iterate(node::Reverse{GreenTreeCursor},
                              next_idx::UInt32 = node.itr.position-UInt32(1))::Union{Nothing, Tuple{GreenTreeCursor, UInt32}}
    node = node.itr
    next_idx == node.position - this(node).node_span - UInt32(1) && return nothing
    next_node = GreenTreeCursor(node.parser_output, next_idx)
    new_next_idx = next_idx - this(next_node).node_span - UInt32(1)
    return (next_node, new_next_idx)
end

# Accessors / predicates
is_leaf(node::GreenTreeCursor)     = !is_non_terminal(this(node))
head(node::GreenTreeCursor)        = this(node).head
treesize(node::GreenTreeCursor)    = this(node).node_span

"""
    span(node)

Get the number of bytes this node covers in the source text.
"""
span(node::GreenTreeCursor) = this(node).byte_span

"""
    RedTreeCursor

Wraps a `GreenTreeCursor` to keep track of the absolute position of the node
in the original source text.
"""
struct RedTreeCursor
    green::GreenTreeCursor
    # The last byte that is still part of the node
    byte_end::UInt32
end
RedTreeCursor(stream::ParseStream) = RedTreeCursor(
    GreenTreeCursor(stream), stream.next_byte - UInt32(1))

Base.reverse(node::RedTreeCursor) = Base.Iterators.Reverse(node)
Base.IteratorSize(::Type{Reverse{RedTreeCursor}}) = Base.SizeUnknown()
@inline function Base.iterate(
        node::Reverse{RedTreeCursor},
        (next_byte_end, next_idx)::NTuple{2, UInt32} =
            (node.itr.byte_end, node.itr.green.position-UInt32(1)))::Union{Nothing, Tuple{RedTreeCursor, NTuple{2, UInt32}}}
    r = iterate(Reverse(node.itr.green), next_idx)
    r === nothing && return nothing
    next_node, next_idx = r
    return RedTreeCursor(next_node, next_byte_end),
           (next_byte_end - span(next_node), next_idx)
end

is_leaf(node::RedTreeCursor)     = is_leaf(node.green)
head(node::RedTreeCursor)        = head(node.green)
span(node::RedTreeCursor)        = span(node.green)
byte_range(node::RedTreeCursor)  = (node.byte_end - span(node.green) + UInt32(1)):node.byte_end
treesize(node::RedTreeCursor)    = treesize(node.green)

function Base.show(io::IO, node::RedTreeCursor)
    print(io, node.green, " [", byte_range(node), "]")
end
