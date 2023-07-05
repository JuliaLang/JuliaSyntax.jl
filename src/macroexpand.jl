# This is the type of syntax literals which macros will manipulate.
# Unlike Expr it includes the module so that hygiene can be automatic
#
# TODO: Maybe we should put `mod` into SourceFile instead, or equivalent?
# This is nice as we
#   1. Don't need a new syntax literal type separate from the unscoped AST type
#   2. Don't need to do all the wrapping we do here
# But it's also not nice because we need to reallocate that whole part of the
# tree and we wouldn't later be able to use a compressed GreenNode inside a
# lazy tree to store those parts of the AST...
struct SyntaxLiteral
    mod::Module
    tree::SyntaxNode
end

children(ex::SyntaxLiteral) = (SyntaxLiteral(ex.mod, c) for c in children(ex.tree))
haschildren(ex::SyntaxLiteral) = haschildren(ex.tree)
numchildren(ex::SyntaxLiteral) = numchildren(ex.tree)
child(ex::SyntaxLiteral, path::Int...) = SyntaxLiteral(ex.mod, child(ex.tree, path...))

head(ex::SyntaxLiteral) = head(ex.tree)
span(ex::SyntaxLiteral) = span(ex.tree)
Base.getindex(ex::SyntaxLiteral, i::Integer) = SyntaxLiteral(ex.mod, getindex(ex.tree, i))
Base.lastindex(ex::SyntaxLiteral) = lastindex(ex.tree)

function Base.getindex(ex::SyntaxLiteral)
    val = ex.tree.val
    if kind(ex) == K"Identifier"
        GlobalRef(ex.mod, val)
    else
        val
    end
end

function Base.show(io::IO, mime::MIME"text/plain", ex::SyntaxLiteral)
    print(io, "SyntaxLiteral in module $(ex.mod):\n")
    show(io, mime, ex.tree)
end

function _syntax_literal(mod, expr)
    SyntaxLiteral(mod, expr)
end

function SyntaxNode(ex::SyntaxLiteral)
    SyntaxNode(K"hygienic_scope", [ex.tree, SyntaxNode(K"Value", ex.mod)];
               srcref=ex.tree)
end

#-------------------------------------------------------------------------------

function _make_syntax_node(mod, srcref, children...)
    cs = SyntaxNode[]
    for c in children
        if c isa SyntaxNode
            push!(cs, c)
        elseif c isa SyntaxLiteral
            push!(cs, SyntaxNode(c))
        else
            push!(cs, SyntaxNode(K"Value", c, srcref=c))
        end
    end
    sr = srcref isa SyntaxLiteral ? srcref.tree : srcref
    SyntaxLiteral(mod, SyntaxNode(head(srcref), cs, srcref=sr))
end

is_identifier(ex::AbstractSyntaxNode) = is_identifier(kind(ex))
is_identifier(k::Kind) = (k == K"Identifier" || k == K"var")

function contains_active_interp(ex, depth)
    k = kind(ex)
    if k == K"$" && depth == 0
        return true
    end

    child_depth = k == K"quote" ? depth + 1 :
                  k == K"$"     ? depth - 1 :
                  depth
    return any(contains_active_interp(c, child_depth) for c in children(ex))
end

function expand_quasiquote(mod, expr, depth=0)
    if !contains_active_interp(expr, depth)
        # TODO: Make copyast unnecessary?
        return SyntaxNode(K"call",
                          SyntaxNode[
                              SyntaxNode(K"Value", _syntax_literal; srcref=expr),
                              SyntaxNode(K"Value", mod;             srcref=expr),
                              SyntaxNode(K"Value", expr;            srcref=expr),
                          ],
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
        if k == K"$" && child_depth == 0
            append!(expanded_children, children(ex))
        else
            push!(expanded_children, expand_quasiquote(mod, ex, child_depth))
        end
    end

    call_args = SyntaxNode[
        SyntaxNode(K"Value", _make_syntax_node; srcref=expr),
        SyntaxNode(K"Value", mod;               srcref=expr),
        SyntaxNode(K"Value", expr;              srcref=expr),
        expanded_children...
    ]
    return SyntaxNode(K"call", call_args, srcref=expr)
end

function needs_expansion(ex)
    k = kind(ex)
    if (k == K"quote" && kind(ex[1]) ∉ KSet"var Identifier") || k == K"macrocall"
        return true
    elseif k == K"module" # || k == K"inert" ???
        return false
    else
        return any(needs_expansion, children(ex))
    end
end

function macroexpand(mod, ex)
    if !needs_expansion(ex)
        return ex
    end

    if kind(ex) == K"quote"
        expand_quasiquote(mod, ex[1])
    elseif kind(ex) == K"macrocall"
        macname = ex[1]
        macfunc = Base.eval(mod, Expr(macname))
        new_call_arg_types =
            Tuple{SyntaxNode, Module, ntuple(_->SyntaxNode, numchildren(ex)-1)...}
        if hasmethod(macfunc, new_call_arg_types, world=Base.get_world_counter())
            margs = [SyntaxLiteral(mod, e) for e in children(ex)[2:end]]
            result = invokelatest(macfunc, macname, mod, margs...)
            return result isa SyntaxLiteral ?
                   SyntaxNode(result) :
                   SyntaxNode(K"Value", result)
        else
            # Attempt to invoke as an old-style macro
            result = Base.macroexpand(mod, Expr(ex))
            return SyntaxNode(K"Value", result)
        end
    else
        SyntaxNode(head(ex), [macroexpand(mod, c) for c in children(ex)]; srcref=ex)
    end
end

#-------------------------------------------------------------------------------

function _needs_lowering(ex)
    if !haschildren(ex)
        return false
    elseif kind(ex) == K"macro"
        return true
    else
        return any(_needs_lowering, children(ex))
    end
end

# Custom lowering using SyntaxNode, before we pass to Julia's normal lowering
function lower(mod, ex)
    if !_needs_lowering(ex)
        return ex
    end
    cs = map(e->lower(mod, e), children(ex))
    if kind(ex) == K"macro"
        # Special lowering for new-style macros :-)
        macname = Symbol("@", ex[1][1].val)
        callex = ex[1]
        callex_cs = copy(children(callex))
        callex_cs[1] = SyntaxNode(K"Identifier", macname, srcref=callex_cs[1])
        splice!(callex_cs, 2:1,
                [
                SyntaxNode(K"::", [
                    SyntaxNode(K"Identifier", :__macroname__, srcref=callex),
                    SyntaxNode(K"Value", SyntaxNode, srcref=callex)
                ], srcref=callex),
                SyntaxNode(K"::", [
                    SyntaxNode(K"Identifier", :__module__, srcref=callex),
                    SyntaxNode(K"Identifier", :Module, srcref=callex)
                ], srcref=callex),
                ]
               )
        return SyntaxNode(K"function",
                          [SyntaxNode(K"call", callex_cs, srcref=callex), ex[2]],
                          srcref=ex)
    end
    SyntaxNode(head(ex), map(e->lower(mod, e), children(e)), srcref=ex)
end

function expand(mod, ex)
    ex = macroexpand(mod, ex)
    lower(mod, ex)
end

#-------------------------------------------------------------------------------
function _can_eval(ex)
    k = kind(ex)
    if !haschildren(ex) || k == K"quote" || k == K"inert"
        return true
    elseif k == K"module"
        # Can't handle modules inside blocks...
        return false
    else
        return all(_can_eval, children(ex))
    end
end

function eval2(mod, ex::SyntaxNode)
    k = kind(ex)
    if k == K"toplevel"
        for e in children(ex)
            eval2(mod, e)
        end
    elseif k == K"module"
        std_imports = !has_flags(ex, BARE_MODULE_FLAG)
        newmod = Base.eval(mod, Expr(:module, std_imports, ex[1].val, Expr(:block)))
        for e in children(ex[2])
            eval2(newmod, e)
        end
    else
        @assert _can_eval(ex)
        e = Expr(expand(mod, ex))
        Base.eval(mod, e)
    end
end

function include2(mod, filename)
    path, prev = Base._include_dependency(mod, filename)
    code = read(path, String)
    tls = task_local_storage()
    tls[:SOURCE_PATH] = path
    try
        return include_string(mod, code; filename=path)
    finally
        if prev === nothing
            delete!(tls, :SOURCE_PATH)
        else
            tls[:SOURCE_PATH] = prev
        end
    end
end

function include_string(mod, str; filename=nothing)
    eval2(mod, parseall(SyntaxNode, str; filename=filename))
end

