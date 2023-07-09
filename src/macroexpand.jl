struct ScopeSpec
    mod::Module
    is_global::Bool
end

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
    scope::ScopeSpec
    tree::SyntaxNode

    function SyntaxLiteral(scope::ScopeSpec, tree::SyntaxNode)
        while kind(tree) == K"hygienic_scope"
            scope = valueof(tree[2])
            tree = tree[1]
        end
        return new(scope, tree)
    end
end

children(ex::SyntaxLiteral) = (child(ex.scope, i) for i in 1:numchildren(tree))
haschildren(ex::SyntaxLiteral) = haschildren(ex.tree)
numchildren(ex::SyntaxLiteral) = numchildren(ex.tree)

function child(ex::SyntaxLiteral, path::Int...)
    # Somewhat awkward way to prevent macros from ever seeing the special
    # K"hygienic_scope" expression.
    #
    # We could avoid this unwrapping if we were willing to stash the module
    # inside the source instead.
    s = ex.scope
    e = ex.tree
    for i in path
        e = e[i]
        while kind(e) == K"hygienic_scope"
            s = e[2]
            e = e[1]
        end
    end
    SyntaxLiteral(s, e)
end

head(ex::SyntaxLiteral) = head(ex.tree)
span(ex::SyntaxLiteral) = span(ex.tree)
Base.getindex(ex::SyntaxLiteral, i::Integer) = child(ex, i)
Base.lastindex(ex::SyntaxLiteral) = lastindex(ex.tree)

# TODO: Should this return val without a scope, or should it return a GlobalRef?
# TODO: Decide between this and the 0-arg getindex
valueof(ex::SyntaxLiteral) = valueof(ex.tree)
valueof(ex::SyntaxNode) = ex.val

function Base.getindex(ex::SyntaxLiteral)
    val = ex.tree.val
    if kind(ex) == K"Identifier"
        GlobalRef(ex.scope, val)
    else
        val
    end
end

function Base.show(io::IO, mime::MIME"text/plain", ex::SyntaxLiteral)
    print(io, "SyntaxLiteral in scope $(ex.scope):\n")
    show(io, mime, ex.tree)
end

function _syntax_literal(scope, expr)
    # The copy here should do similar to `copyast` ?
    SyntaxLiteral(scope, copy(expr))
end

function SyntaxNode(ex::SyntaxLiteral)
    SyntaxNode(K"hygienic_scope", [ex.tree, SyntaxNode(K"Value", ex.scope)];
               srcref=ex.tree)
end

#-------------------------------------------------------------------------------

function _make_syntax_node(scope, srcref, children...)
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
    SyntaxLiteral(scope, SyntaxNode(head(srcref), cs, srcref=sr))
end

function contains_active_interp(ex, depth)
    k = kind(ex)
    if k == K"$" && depth == 0
        return true
    end

    inner_depth = k == K"quote" ? depth + 1 :
                  k == K"$"     ? depth - 1 :
                  depth
    return any(contains_active_interp(c, inner_depth) for c in children(ex))
end

function expand_quasiquote_content(mod, ex, depth)
    if !contains_active_interp(ex, depth)
        # TODO: Should we do this lowering here as a part of macro expansion?
        # Or would it be neater to lower to an intermediate AST form instead,
        # with lowering to actual calls to _syntax_literal in "lowering
        # proper"? Same question further down...
        return SyntaxNode(K"call",
                          SyntaxNode[
                              SyntaxNode(K"Value", _syntax_literal;      srcref=ex),
                              SyntaxNode(K"Value", ScopeSpec(mod, true); srcref=ex),
                              SyntaxNode(K"Value", ex;                   srcref=ex),
                          ],
                          srcref=ex)
    end

    # We have an interpolation deeper in the tree somewhere - expand to an
    # expression 
    inner_depth = kind(ex) == K"quote" ? depth + 1 :
                  kind(ex) == K"$"     ? depth - 1 :
                  depth
    expanded_children = SyntaxNode[]
    for e in children(ex)
        if kind(e) == K"$" && inner_depth == 0
            append!(expanded_children, children(e))
        else
            push!(expanded_children, expand_quasiquote_content(mod, e, inner_depth))
        end
    end

    call_args = SyntaxNode[
        SyntaxNode(K"Value", _make_syntax_node;    srcref=ex),
        SyntaxNode(K"Value", ScopeSpec(mod, true); srcref=ex),
        SyntaxNode(K"Value", ex;                   srcref=ex),
        expanded_children...
    ]
    return SyntaxNode(K"call", call_args, srcref=ex)
end

function expand_quasiquote(mod, ex)
    if kind(ex) == K"$"
        if kind(ex[1]) == K"..."
            # TODO: Don't throw here - provide diagnostics instead
            error("`...` expression outside of call")
        else
            return ex[1]
        end
    end
    expand_quasiquote_content(mod, ex, 0)
end

function needs_expansion(ex)
    k = kind(ex)
    if (k == K"quote") || k == K"macrocall"
        return true
    elseif k == K"module" # || k == K"inert" ???
        return false
    else
        return any(needs_expansion, children(ex))
    end
end

function macroexpand(mod, ex)
    k = kind(ex)
    if !haschildren(ex) || k == K"inert" || k == K"module" || k == K"meta"
        return ex
    elseif k == K"quote"
        return macroexpand(mod, expand_quasiquote(mod, ex[1]))
    elseif k == K"hygienic_scope"
        scope = valueof(ex[2])
        result = macroexpand(scope.mod, ex[1])
        return SyntaxNode(SyntaxLiteral(scope, result))
    elseif k == K"macrocall"
        macname = ex[1]
        macfunc = eval2(mod, macname)
        new_call_arg_types =
            Tuple{SyntaxNode, Module, ntuple(_->SyntaxNode, numchildren(ex)-1)...}
        if hasmethod(macfunc, new_call_arg_types, world=Base.get_world_counter())
            margs = [SyntaxLiteral(ScopeSpec(mod, false), e)
                     for e in children(ex)[2:end]]
            expanded = invokelatest(macfunc, macname, mod, margs...)
            expanded = expanded isa SyntaxLiteral ?
                   SyntaxNode(expanded) :
                   SyntaxNode(K"Value", expanded, srcref=ex)
            result = macroexpand(mod, expanded)
            return result
        else
            # Attempt to invoke as an old-style macro
            result = Base.macroexpand(mod, Expr(ex))
            return SyntaxNode(K"Value", result, srcref=ex)
        end
    else
        return SyntaxNode(head(ex), [macroexpand(mod, c) for c in children(ex)]; srcref=ex)
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

# Insert Expr(:esc) expressions to escape any `(scope ex nothing)` expressions
# to the outer containing scope.
function _insert_scope_escapes!(ex, depth)
    if !(ex isa Expr)
        return ex
    end
    ex::Expr
    if ex.head == :hygienic_scope
        scope = ex.args[2]
        if scope.is_global
            return Expr(Symbol("hygienic-scope"),
                        _insert_scope_escapes!(ex.args[1], depth + 1),
                        scope.mod)
        else
            x = ex.args[1]
            for i=1:depth
                x = esc(x)
            end
            return x
        end
    else
        map!(e->_insert_scope_escapes!(e, depth), ex.args, ex.args)
        return ex
    end
end

function expand(::Type{Expr}, mod, ex)
    _insert_scope_escapes!(Expr(expand(mod, ex)), 0)
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
        if std_imports
            # JuliaSyntax-specific imports
            Base.eval(newmod, :(using JuliaSyntax: @__EXTENSIONS__))
        end
        for e in children(ex[2])
            eval2(newmod, e)
        end
    else
        if get_extension(mod, :new_macros, false)
            @assert _can_eval(ex)
            # NB: Base throws LoadError with a misleading line in this
            # implementation of eval (which doesn't include LineNumberNodes which
            # are normally a part of :toplevel or :module Expr's).
            # Best fix: remove LoadError!  Alternative fix: add line numbers...
            e = expand(Expr, mod, ex)
        else
            e = Expr(ex)
        end
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

_extensions_var = Symbol("##__EXTENSIONS__")

function get_extension(mod::Module, key::Symbol, default=nothing)
    while true
        if isdefined(mod, _extensions_var)
            d = getfield(mod, _extensions_var)
            if haskey(d, key)
                return d[key]
            end
        end
        pmod = parentmodule(mod)
        if pmod == mod
            break
        end
        mod = pmod
    end
    return default
end

"""
    @__EXTENSIONS__ new_macros=true
"""
macro __EXTENSIONS__(exs...)
    kvs = Any[]
    for e in exs
        @assert Meta.isexpr(e, :(=), 2)
        @assert e.args[1] isa Symbol
        push!(kvs, Expr(:call, :(=>), QuoteNode(e.args[1]), esc(e.args[2])))
    end
    # TODO: Might this better expand to `Expr(:meta)` if module extensions were
    # supported in the runtime?
    :(const $(esc(_extensions_var)) = Dict{Symbol,Any}($(kvs...)))
end

