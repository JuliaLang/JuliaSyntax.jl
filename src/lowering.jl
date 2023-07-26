# Experimental port of some parts of Julia's code lowering (ie, the symbolic
# non-type-related compiler passes)

#-------------------------------------------------------------------------------
# Utilities

struct ExpansionContext
    next_ssa_label::Ref{Int}
end

ExpansionContext() = ExpansionContext(Ref(0))

function Identifier(val, srcref)
    SyntaxNode(K"Identifier", val, srcref=srcref)
end

function SSALabel(ctx, srcref)
    val = ctx.next_ssa_label[]
    ctx.next_ssa_label[] += 1
    SyntaxNode(K"SSALabel", val, srcref=srcref)
end


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

function expand_assignment(ctx, ex)
end

function expand_forms(ctx, ex)
    k = kind(ex)
    if k == K"while"
        SyntaxNode(K"break_block", ex, [
            Identifier(:loop_exit, ex), # Should this refer syntactically to the `end`?
            SyntaxNode(K"_while", ex, [
                expand_condition(ctx, ex[1]),
                SyntaxNode(K"break_block", ex, [
                    Identifier(:loop_cont, ex[2]),
                    SyntaxNode(K"scope_block", ex[2], [
                        blockify(expand_forms(ctx, ex[2]))
                    ])
                ])
            ])
        ])
    elseif !haschildren(ex)
        ex
    else
        if k == K"=" && (numchildren(ex) != 2 && kind(ex[1]) != K"Identifier")
            error("TODO")
        end
        SyntaxNode(head(ex), map(e->expand_forms(ctx,e), children(ex)), srcref=ex)
    end
end

#-------------------------------------------------------------------------------
# Pass 2: Identify and rename local vars

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
# * Or alternatively / more easily, desugar by replacment ??
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

struct ScopeInfo
    lambda_vars::Union{LambdaLocals,LambdaVars}
    parent::Union{Nothing,ScopeInfo}
    args::Set{Symbol}
    locals::Set{Symbol}
    globals::Set{Symbol}
    static_params::Set{Symbol}
    renames::Dict{Symbol,Symbol}
    implicit_globals::Set{Symbol}
    warn_vars::Set{Symbol}
    is_soft::Bool
    is_hard::Bool
    table::Dict{Symbol,Any}
end

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
# Pass 3: analyze variables
#
# This pass records information about variables used by closure conversion.
# finds which variables are assigned or captured, and records variable
# type declarations.
#
# This info is recorded by setting the second argument of `lambda` expressions
# in-place to
#   (var-info-lst captured-var-infos ssavalues static_params)
# where var-info-lst is a list of var-info records

#-------------------------------------------------------------------------------
# Pass 4: closure conversion
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

