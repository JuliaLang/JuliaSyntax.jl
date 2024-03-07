# Lowering pass 2: analyze scopes (passes 2/3 in flisp code)
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

#-------------------------------------------------------------------------------
# AST traversal functions - useful for performing non-recursive AST traversals
function _schedule_traverse(stack, e)
    push!(stack, e.id)
    return nothing
end
function _schedule_traverse(stack, es::Union{Tuple,Vector,Base.Generator})
    append!(stack, (e.id for e in es))
    return nothing
end

function traverse_ast(f, ex::SyntaxTree)
    graph = ex.graph
    todo = NodeId[ex.id]
    while !isempty(todo)
        e1 = pop!(todo)
        f(SyntaxTree(graph, e1), e->_schedule_traverse(todo, e))
    end
end

function find_in_ast(f, ex::SyntaxTree)
    graph = ex.graph
    todo = [ex.id]
    while !isempty(todo)
        e1 = pop!(todo)
        res = f(SyntaxTree(graph,e1), e->_schedule_traverse(todo, e))
        if !isnothing(res)
            return res
        end
    end
    return nothing
end

# NB: This only really works after expand_forms has already processed assignments.
function find_assigned_vars(ex)
    vars = Vector{typeof(ex)}()
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == K"method"
            TODO(e, "method")
            return nothing
        elseif k == K"="
            v = decl_var(e[1])
            if !(kind(v) in KSet"SSALabel globalref outerref" || is_placeholder(e))
                push!(vars, v)
            end
            traverse(e[2])
        else
            traverse(children(e))
        end
    end
    var_names = [v.name_val for v in vars]
    return unique(var_names)
end

function find_decls(decl_kind, ex)
    vars = Vector{typeof(ex)}()
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == decl_kind
            if !is_placeholder(e[1])
                push!(vars, decl_var(e[1]))
            end
        else
            traverse(children(e))
        end
    end
    var_names = [v.name_val for v in vars]
    return unique(var_names)
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

# TODO:
# Incorporate hygenic-scope here so we always have a parent scope when
# processing variables

# Steps
# 1. Deal with implicit locals and globals only
# 2. Add local, global etc later

# struct LambdaVars
#     # For analyze-variables pass
#     # var_info_lst::Set{Tuple{Symbol,Symbol}} # ish?
#     # captured_var_infos ??
#     # ssalabels::Set{SSALabel}
#     # static_params::Set{Symbol}
# end

struct LambdaInfo
    arg_names::Vector{NodeId}
    return_type::Union{Nothing,NodeId}
    arg_vars::Set{VarId}
    body_vars::Set{VarId}
end

function LambdaInfo(args, return_type)
    LambdaInfo([_node_id(a) for a in args],
               isnothing(return_type) ? nothing : _node_id(return_type),
               Set{VarId}(),
               Set{VarId}())
end

function resolve_scopes(ctx, ex)
    thk_vars = LambdaInfo()
    resolve_scopes(ctx, thk_vars, ex)
end

function resolve_scopes(ctx, lambda_vars, ex)
    k = kind(ex)
    if k == K"Identifier"
        # Look up identifier
        name = ex.name_val
        for s in Iterators.reverse(ctx.scope_stack)
        end
    elseif k == K"global"
        TODO("global")
    elseif k == K"local" || k == K"local_def"
        TODO("local") # Remove these
    # TODO
    # elseif require_existing_local
    # elseif locals # return Dict of locals
    # elseif islocal
    elseif k == K"lambda"
        vars = LambdaInfo(ex[1])
        resolve_scopes(ctx, vars, ex[2])
    elseif hasattr(ex, :scope)
        # scope-block
    end
    # scope = get(ex, :scope, nothing)
    # if !isnothing(scope)
    # for e in children(ex)
    #     resolve_scopes(ctx, child_scope, e)
    # end
end

