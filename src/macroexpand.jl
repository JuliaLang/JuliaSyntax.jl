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
#
# TODO: Maybe rename to just `Syntax`?
struct SyntaxLiteral
    scope::Union{Nothing,ScopeSpec}
    tree::SyntaxNode

    function SyntaxLiteral(scope::Union{Nothing,ScopeSpec}, tree::SyntaxNode)
        while kind(tree) == K"hygienic_scope"
            scope = valueof(tree[2])
            tree = tree[1]
        end
        return new(scope, tree)
    end
end

function SyntaxLiteral(h::Union{Kind,SyntaxHead}, srcref::SyntaxLiteral, children)
    # There's no meaning We don't care about the scope here right? Right??
    s1 = first(children).scope
    if all(c.scope == s1 for c in children)
        SyntaxLiteral(s1, SyntaxNode(h, srcref.tree, [c.tree for c in children]))
    else
        SyntaxLiteral(nothing, SyntaxNode(h, srcref.tree, [SyntaxNode(c) for c in children]))
    end
end

function SyntaxLiteral(h::Union{Kind,SyntaxHead}, scope::Union{Nothing,ScopeSpec},
                       srcref::SyntaxLiteral, val)
    SyntaxLiteral(scope, SyntaxNode(h, srcref.tree, val))
end


function Base.iterate(ex::SyntaxLiteral)
    if numchildren(ex) == 0
        return nothing
    end
    return (child(ex,1), 1)
end

function Base.iterate(ex::SyntaxLiteral, i)
    i += 1
    if i > numchildren(ex)
        return nothing
    else
        return (child(ex, i), i)
    end
end

children(ex::SyntaxLiteral) = (SyntaxLiteral(ex.scope, c) for c in children(ex.tree))
haschildren(ex::SyntaxLiteral) = haschildren(ex.tree)
numchildren(ex::SyntaxLiteral) = numchildren(ex.tree)

Base.range(ex::SyntaxLiteral) = range(ex.tree)

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
    print(io, "SyntaxLiteral")
    if !isnothing(ex.scope)
        print(io, " in ", ex.scope.mod, " ", ex.scope.is_global ? "macro" : "macrocall", " scope")
    else
        print(io, " without scope")
    end
    print(io, ":\n")
    show(io, mime, ex.tree)
end

function _syntax_literal(scope, expr)
    # The copy here should do similar to `copyast` ?
    SyntaxLiteral(scope, copy(expr))
end

function SyntaxNode(ex::SyntaxLiteral)
    if isnothing(ex.scope)
        ex.tree
    else
        SyntaxNode(K"hygienic_scope", ex.tree, [ex.tree, SyntaxNode(K"Value", ex.scope)])
    end
end

struct MacroContext
    macroname::SyntaxNode
    mod::Module
    # TODO: For warnings, we could have a diagnostics field here in the macro
    # context too? Or maybe macros could just use @warn for that?
end

#-------------------------------------------------------------------------------

struct MacroExpansionError
    context::Union{Nothing,MacroContext}
    diagnostics::Diagnostics
end

function MacroExpansionError(context::Union{Nothing,MacroContext},
        ex::Union{SyntaxNode,SyntaxLiteral}, msg::String; kws...)
    diagnostics = Diagnostics()
    emit_diagnostic(diagnostics, ex; error=msg, kws...)
    MacroExpansionError(context, diagnostics)
end

function MacroExpansionError(diagnostics::Diagnostics)
    MacroExpansionError(nothing, diagnostics)
end

function MacroExpansionError(ex::Union{SyntaxNode,SyntaxLiteral}, msg::String; kws...)
    MacroExpansionError(nothing, ex, msg; kws...)
end

function Base.showerror(io::IO, exc::MacroExpansionError)
    print(io, "MacroExpansionError")
    ctx = exc.context
    if !isnothing(ctx)
        print(io, " while expanding ", ctx.macroname,
              " in module ", ctx.mod)
    end
    print(io, ":\n")
    show_diagnostics(io, exc.diagnostics)
end

function emit_diagnostic(diagnostics::Diagnostics, ex::SyntaxNode; before=false, after=false, kws...)
    # TODO: Do we really want this diagnostic representation? Source ranges are
    # flexible, but it seems we loose something by not keeping the offending
    # expression `ex` somewhere?
    #
    # An alternative could be to allow diagnostic variants TextDiagnostic and
    # TreeDiagnostic or something?
    r = range(ex)
    if before
        r = first(r):first(r)-1
    elseif after
        r = last(r)+1:last(r)
    end
    diagnostic = Diagnostic(first(r), last(r); kws...)
    push!(diagnostics, (ex.source, diagnostic))
end

function emit_diagnostic(diagnostics::Diagnostics, ex::SyntaxLiteral; kws...)
    emit_diagnostic(diagnostics, ex.tree; kws...)
end

#-------------------------------------------------------------------------------

function _make_syntax_node(scope, srcref, children...)
    same_scope = all(!(c isa SyntaxLiteral) || c.scope == scope for c in children)
    cs = SyntaxNode[]
    for c in children
        if c isa SyntaxLiteral
            push!(cs, same_scope ? c.tree : SyntaxNode(c))
        else
            push!(cs, SyntaxNode(K"Value", srcref, c))
        end
    end
    sr = srcref isa SyntaxLiteral ? srcref.tree : srcref
    h = kind(srcref) == K"$" ? SyntaxHead(K"Value") : head(srcref)
    SyntaxLiteral(scope, SyntaxNode(h, sr, cs))
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
        return SyntaxNode(K"call", ex,
                          SyntaxNode[
                              SyntaxNode(K"Value", ex, _syntax_literal),
                              SyntaxNode(K"Value", ex, ScopeSpec(mod, true)),
                              SyntaxNode(K"Value", ex, ex)
                          ])
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

    return SyntaxNode(K"call", ex, SyntaxNode[
        SyntaxNode(K"Value", ex, _make_syntax_node),
        SyntaxNode(K"Value", ex, ScopeSpec(mod, true)),
        SyntaxNode(K"Value", ex, ex),
        expanded_children...
    ])
end

function expand_quasiquote(mod, ex)
    if kind(ex) == K"$"
        if kind(ex[1]) == K"..."
            # TODO: Don't throw here - provide diagnostics instead
            error("`...` expression outside of call")
        else
            r = SyntaxNode(K"call", ex, SyntaxNode[
                    SyntaxNode(K"Value", ex, _make_syntax_node),
                    SyntaxNode(K"Value", ex, ScopeSpec(mod, true)),
                    SyntaxNode(K"Value", ex, ex),
                    ex[1]
                ])
            return r
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

function macroexpand(mod::Module, ex::SyntaxNode)
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
            Tuple{MacroContext, ntuple(_->SyntaxNode, numchildren(ex)-1)...}
        if hasmethod(macfunc, new_call_arg_types, world=Base.get_world_counter())
            margs = [SyntaxLiteral(ScopeSpec(mod, false), e)
                     for e in children(ex)[2:end]]
            ctx = MacroContext(macname, mod)
            expanded = try
                invokelatest(macfunc, ctx, margs...)
            catch exc
                if exc isa MacroExpansionError
                    # Add context to the error
                    rethrow(MacroExpansionError(ctx, exc.diagnostics))
                else
                    throw(MacroExpansionError(ctx, ex, "Error expanding macro"))
                end
            end
            expanded = expanded isa SyntaxLiteral ?
                   SyntaxNode(expanded) :
                   SyntaxNode(K"Value", ex, expanded)
            result = macroexpand(mod, expanded)
            return result
        else
            # Attempt to invoke as an old-style macro
            result = Base.macroexpand(mod, Expr(ex))
            return SyntaxNode(K"Value", ex, result)
        end
    else
        return SyntaxNode(head(ex), ex, [macroexpand(mod, c) for c in children(ex)])
    end
end

function macroexpand(ex::SyntaxLiteral)
    macroexpand(ex.scope.mod, ex.tree)
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
        callex_cs[1] = SyntaxNode(K"Identifier", callex_cs[1], macname)
        insert!(callex_cs, 2,
                SyntaxNode(K"::", callex, [
                    SyntaxNode(K"Identifier", callex, :__context__)
                    SyntaxNode(K"Value", callex, MacroContext)
                ]))
        return SyntaxNode(K"function", ex,
                          [SyntaxNode(K"call", callex, callex_cs), ex[2]])
    end
    SyntaxNode(head(ex), ex, map(e->lower(mod, e), children(e)))
end

function expand(mod, ex)
    ex = macroexpand(mod, ex)
    lower(mod, ex)
end

# Insert Expr(:esc) expressions to escape any `(scope ex nothing)` expressions
# to the outer containing scope.
function _fix_scopes!(ex, depth)
    if !(ex isa Expr)
        return ex
    end
    ex::Expr
    if ex.head == :hygienic_scope
        scope = ex.args[2]
        if scope.is_global
            return Expr(Symbol("hygienic-scope"),
                        _fix_scopes!(ex.args[1], depth + 1),
                        scope.mod)
        else
            x = ex.args[1]
            for i=1:depth
                x = esc(x)
            end
            return x
        end
    else
        map!(e->_fix_scopes!(e, depth), ex.args, ex.args)
        return ex
    end
end

function expand(::Type{Expr}, mod, ex)
    _fix_scopes!(Expr(expand(mod, ex)), 0)
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
    result = nothing
    if k == K"toplevel"
        for e in children(ex)
            result = eval2(mod, e)
        end
    elseif k == K"module"
        std_imports = !has_flags(ex, BARE_MODULE_FLAG)
        newmod = Base.eval(mod, Expr(:module, std_imports, ex[1].val, Expr(:block)))
        if std_imports
            # JuliaSyntax-specific imports
            Base.eval(newmod, quote
                using JuliaSyntax: @__EXTENSIONS__
                eval(x::$SyntaxLiteral) = $eval2(x)
            end)
        end
        stmts = children(ex[2])
        first_stmt = 1
        if !isempty(stmts) && kind(stmts[1]) == K"macrocall" &&
                valueof(stmts[1][1]) == Symbol("@__EXTENSIONS__")
            result = eval2(newmod, stmts[1])
            first_stmt += 1
            if get_extension(newmod, :new_macros, false) && std_imports
                # Override include() for the module
                Base.eval(newmod, :(include(path) = $(JuliaSyntax.include2)($newmod, path)))
            end
        end
        for e in stmts[first_stmt:end]
            result = eval2(newmod, e)
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
        result = Base.eval(mod, e)
    end
    return result
end

function eval2(ex::SyntaxLiteral)
    eval2(ex.scope.mod, ex.tree)
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

function set_extension(mod::Module; kws...)
    if !isdefined(mod, _extensions_var)
        Base.eval(mod, :(const $(_extensions_var) = $(Dict{Symbol,Any}())))
    end
    d = getfield(mod, _extensions_var)
    for kv in kws
        push!(d, kv)
    end
end

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
        push!(kvs, Expr(:kw, e.args[1], esc(e.args[2])))
    end
    # TODO: Expand to an `Expr(:meta)` in the future?
    :(set_extension(@__MODULE__(), $(kvs...)))
end

