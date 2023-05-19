using JuliaSyntax
using JuliaSyntax: SyntaxNode, @K_str, children, child, haschildren, kind, head, sourcetext, highlight
using ReplMaker

function single_match(matches, ex, pat)
    matched = false
    if kind(pat[1]) == K"Identifier"
        name = pat[1].val
        matched = true
    elseif kind(pat[1]) == K"block"
        @assert length(children(pat[1])) == 2
        name = pat[1][1].val
        pred = Expr(pat[1][2])
        # lol `eval`. we need pattern compilation
        matched = eval(:(let $name = $ex
                              $pred
                          end))
    end
    if matched
        push!(matches, name=>ex)
    end
    return matched
end

function match_syntax(matches, ex, pat)
    if kind(pat) == K"$"
        return single_match(matches, ex, pat)
    elseif head(ex) == head(pat)
        if !haschildren(ex) && !haschildren(pat)
            # Is this right?
            return ex.val == pat.val
        end
        ex_cs  = children(ex)
        pat_cs = children(pat)
        i = 1
        j = 1
        while i <= length(ex_cs) && j <= length(pat_cs)
            pc = pat_cs[j]
            ec = ex_cs[i]
            if kind(pc) == K"$"
                if kind(pc[1]) == K"..."
                    # TODO: Slurp will need some tricky handling for patterns like, eg,
                    # f(x, $(as...), z, $(bs...))
                    push!(matches, pc[1][1].val=>ex_cs[i:end])
                    i = length(ex_cs)
                else
                    if !single_match(matches, ec, pc)
                        return false
                    end
                end
            else
                if !match_syntax(matches, ec, pc)
                    return false
                end
            end
            i += 1
            j += 1
        end
        return j == length(pat_cs) + 1
    else
        return false
    end
end

function _find_syntax(match_set, ex, pat)
    matches = []
    if match_syntax(matches, ex, pat)
        push!(match_set, (node=ex, bindings=matches))
    else
        for c in children(ex)
            _find_syntax(match_set, c, pat)
        end
    end
end

function find_syntax(pat::SyntaxNode, ex::SyntaxNode)
    match_set = []
    _find_syntax(match_set, ex, pat)
    return match_set
end

function find_syntax(pat::AbstractString, ex::AbstractString)
    find_syntax(JuliaSyntax.parsestmt(SyntaxNode, pat),
                JuliaSyntax.parseall(SyntaxNode, ex))
end

function find_and_highlight_matches(pat, ex)
    matches = find_syntax(pat, ex)
    for (node, bindings) in matches
        code = sprint(context=:color=>true) do io
            JuliaSyntax.highlight(io, node.source, range(node), context_lines_inner=5)
        end
        @info "Match" bindings Text(code)
    end
end

# find_syntax(raw"$x + $y",
#     """
#     function foo()
#         a + b * c
#         for i = 1:10
#             println(i)
#             println(i + 3)
#         end
#     end
#     """)

@info "# Simple matching"
find_and_highlight_matches(raw"a => $y",
    """
    function foo()
        a=>b
    end

    function bar()
        c=>d
        a=>x+1
        e=>f
    end
    """)

@info "# Underscore bindings match but are ignored"
find_and_highlight_matches(raw"$x + $_",
    """
    function foo()
        a + b * c
        for i = 1:10
            println(i)
            println(i + 3)
        end
    end
    """)

@info "# A pattern like `\$(xs...)` matches remaining arguments"
find_and_highlight_matches(raw"foo(a, $(xs...))",
    """
    let a=1
        foo(a, b, c)
        foo(x, b, c)
    end
    """)


@info """# Custom predicate patterns"""
find_and_highlight_matches(raw"""$(x; kind(x) == K"string")""",
    """
    let a=1
        foo(a, b, "c")
        foo(x, b, c)
        "some string"
    end
    """)

