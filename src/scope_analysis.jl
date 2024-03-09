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

function traverse_ast(f, exs)
    graph = first(exs).graph
    todo = NodeId[e.id for e in exs]
    while !isempty(todo)
        e1 = pop!(todo)
        f(SyntaxTree(graph, e1), e->_schedule_traverse(todo, e))
    end
end

function traverse_ast(f, ex::SyntaxTree)
    traverse_ast(f, (ex,))
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
function find_scope_vars(ex, children_only)
    assigned_vars = Set{String}()
    # TODO:
    # local_vars
    local_def_vars = Set{String}()
    # global_vars
    used_vars = Set{String}()
    traverse_ast(children_only ? children(ex) : ex) do e, traverse
        k = kind(e)
        if k == K"Identifier"
            push!(used_vars, e.name_val)
        elseif !haschildren(e) || hasattr(e, :scope_type) || is_quoted(k) ||
                k in KSet"lambda module toplevel"
            return
        elseif k == K"local_def"
            push!(local_def_vars, e[1].name_val)
        # elseif k == K"method" TODO static parameters
        elseif k == K"="
            v = decl_var(e[1])
            if !(kind(v) in KSet"SSALabel globalref outerref" || is_placeholder(v))
                push!(assigned_vars, v.name_val)
            end
            traverse(e[2])
        else
            traverse(children(e))
        end
    end
    return assigned_vars, local_def_vars, used_vars
end

function find_decls(decl_kind, ex)
    vars = Vector{typeof(ex)}()
    traverse_ast(ex) do e, traverse
        k = kind(e)
        if !haschildren(e) || is_quoted(k) || k in KSet"lambda scope_block module toplevel"
            return
        elseif k == decl_kind
            v = decl_var(e[1])
            if !is_placeholder(v)
                push!(vars, decl_var(v))
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

# struct LambdaVars
#     # For analyze-variables pass
#     # var_info_lst::Set{Tuple{Symbol,Symbol}} # ish?
#     # captured_var_infos ??
#     # ssalabels::Set{SSALabel}
#     # static_params::Set{Symbol}
# end

# Mirror of flisp scope info structure
# struct ScopeInfo
#     lambda_vars::Union{LambdaLocals,LambdaInfo}
#     parent::Union{Nothing,ScopeBlockInfo}
#     args::Set{Symbol}
#     locals::Set{Symbol}
#     globals::Set{Symbol}
#     static_params::Set{Symbol}
#     renames::Dict{Symbol,Symbol}
#     implicit_globals::Set{Symbol}
#     warn_vars::Set{Symbol}
#     is_soft::Bool
#     is_hard::Bool
#     table::Dict{Symbol,Any}
# end

struct ScopeResolutionContext{GraphType}
    graph::GraphType
    next_var_id::Ref{VarId}
    # Stack of name=>id mappings for each scope, innermost scope last.
    var_id_stack::Vector{Dict{String,VarId}}
end

function ScopeResolutionContext(ctx::DesugaringContext)
    ScopeResolutionContext(ctx.graph, ctx.next_var_id, Vector{Dict{String,VarId}}())
end

function lookup_var(ctx, name)
    for i in lastindex(ctx.var_id_stack):-1:1
        ids = ctx.var_id_stack[i]
        id = get(ids, name, nothing)
        if !isnothing(id)
            return id
        end
    end
    return nothing
end

function resolve_scope!(f::Function, ctx, ex, children_only)
    id_map = Dict{String,VarId}()
    assigned, local_def_vars, used_vars = find_scope_vars(ex, children_only)
    for name in local_def_vars
        id_map[name] = new_var_id(ctx)
    end
    for name in assigned
        if !haskey(id_map, name)
            id_map[name] = new_var_id(ctx)
        end
    end
    var_id_stack = ctx.var_id_stack
    outer_scope = isempty(var_id_stack) ? id_map : var_id_stack[1]
    # Things which aren't assigned further up the stack are newly discovered
    # globals
    for name in used_vars
        if !haskey(id_map, name) && isnothing(lookup_var(ctx, name))
            outer_scope[name] = new_var_id(ctx)
        end
    end
    push!(var_id_stack, id_map)
    res = f()
    pop!(var_id_stack)
    return res
end

resolve_scopes!(ctx::DesugaringContext, ex) = resolve_scopes!(ScopeResolutionContext(ctx), ex)

function resolve_scopes!(ctx::ScopeResolutionContext, ex)
    resolve_scope!(ctx, ex, false) do
        resolve_scopes_!(ctx, ex)
    end
end

function resolve_scopes_!(ctx, ex)
    k = kind(ex)
    if k == K"Identifier"
        if is_placeholder(ex)
            return # FIXME - make these K"placeholder"?
        end
        # TODO: Maybe we shouldn't do this in place??
        setattr!(ctx.graph, ex.id, var_id=lookup_var(ctx, ex.name_val))
    elseif !haschildren(ex) || is_quoted(ex) || k == K"toplevel"
        return
    elseif k == K"global"
        TODO("global")
    elseif k == K"local"
        TODO("local")
    # TODO
    # elseif require_existing_local
    # elseif locals # return Dict of locals
    # elseif islocal
    elseif k == K"lambda"
        # TODO: Lambda captures!
        info = ex.lambda_info
        id_map = Dict{String,VarId}()
        for a in info.args
            id_map[a.name_val] = new_var_id(ctx)
        end
        push!(ctx.var_id_stack, id_map)
        for a in info.args
            resolve_scopes!(ctx, a)
        end
        resolve_scopes_!(ctx, ex[1])
        pop!(ctx.var_id_stack)
    elseif k == K"block" && hasattr(ex, :scope_type)
        resolve_scope!(ctx, ex, true) do
            for e in children(ex)
                resolve_scopes_!(ctx, e)
            end
        end
    else
        for e in children(ex)
            resolve_scopes_!(ctx, e)
        end
    end
    ex
end

