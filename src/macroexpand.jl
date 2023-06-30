function _make_syntax_node(srcref, children...)
    SyntaxNode(head(srcref); children, srcref=srcref)
end

is_identifier(ex::AbstractSyntaxNode) = is_identifier(kind(ex))
is_identifier(k::Kind) = (k == K"Identifier" || k == K"var")

function contains_active_interp(ex, depth)
    k = kind(ex)
    if k == K"$" && depth == 1
        return true
    end

    child_depth = k == K"quote" ? depth + 1 :
                  k == K"$"     ? depth - 1 :
                  depth
    return any(contains_active_interp(c, child_depth) for c in children(ex))
end

function expand_quasiquote(expr, depth=0)
    if !contains_active_interp(expr, depth)
        # TODO: Make copyast unnecessary?
        return SyntaxNode(K"copyast",
                          [SyntaxNode(K"inert", [expr], srcref=expr)],
                          srcref=expr)
    end

    # We have an interpolation deeper in the tree somewhere - expand to an
    # expression 
    k = kind(expr)
    child_depth = k == K"quote" ? depth + 1 :
                  k == K"$"     ? depth - 1 :
                  depth
    expanded_children = SyntaxNode[]
    for ex in children(expr)
        k = kind(ex)
        if k == K"$" && child_depth == 1
            append!(expanded_children, children(ex))
        else
            push!(expanded_children, expand_quasiquote(ex, child_depth))
        end
    end

    call_args = SyntaxNode[
        SyntaxNode(K"Value", _make_syntax_node; srcref=expr),
        SyntaxNode(K"Value", expr;              srcref=expr),
        expanded_children...
    ]
    return SyntaxNode(K"call", call_args, srcref=expr)
end
