# Utils

# CodeInfo constructor. TODO: Should be in Core?
function _CodeInfo(code,
         codelocs,
         ssavaluetypes,
         ssaflags,
         method_for_inference_limit_heuristics,
         linetable,
         slotnames,
         slotflags,
         slottypes,
         rettype,
         parent,
         edges,
         min_world,
         max_world,
         inferred,
         propagate_inbounds,
         has_fcall,
         nospecializeinfer,
         inlining,
         constprop,
         purity,
         inlining_cost)
    @eval $(Expr(:new, :(Core.CodeInfo),
           convert(Vector{Any}, code),
           convert(Vector{Int32}, codelocs),
           convert(Any, ssavaluetypes),
           convert(Vector{UInt32}, ssaflags),
           convert(Any, method_for_inference_limit_heuristics),
           convert(Any, linetable),
           convert(Vector{Symbol}, slotnames),
           convert(Vector{UInt8}, slotflags),
           convert(Any, slottypes),
           convert(Any, rettype),
           convert(Any, parent),
           convert(Any, edges),
           convert(UInt64, min_world),
           convert(UInt64, max_world),
           convert(Bool, inferred),
           convert(Bool, propagate_inbounds),
           convert(Bool, has_fcall),
           convert(Bool, nospecializeinfer),
           convert(UInt8, inlining),
           convert(UInt8, constprop),
           convert(UInt16, purity),
           convert(UInt16, inlining_cost)))
end

#-------------------------------------------------------------------------------
# Lowering pass 4: Flatten to linear IR

function is_simple_atom(ex)
    k = kind(ex)
    # FIXME
#   (or (number? x) (string? x) (char? x)
#       (and (pair? x) (memq (car x) '(ssavalue null true false thismodule)))
#       (eq? (typeof x) 'julia_value)))
    is_number(k) || k == K"String" || k == K"Char"
end

# N.B.: This assumes that resolve-scopes has run, so outerref is equivalent to
# a global in the current scope.
function is_valid_ir_argument(ex)
    k = kind(ex)
    return is_simple_atom(ex)
    # FIXME ||
           #(k == K"outerref" && nothrow_julia_global(ex[1]))  ||
           #(k == K"globalref" && nothrow_julia_global(ex))    ||
           #(k == K"quote" || k = K"inert" || k == K"top" ||
            #k == K"core" || k == K"slot" || k = K"static_parameter")
end

"""
Context for creating linear IR.

One of these is created per lambda expression to flatten the body down to
linear IR.
"""
struct LinearIRContext
    graph::SyntaxGraph
    code::Vector{Any}
    next_var_id::Ref{Int}
    lambda_args::Set{VarId}
    return_type::Union{Nothing,NodeId}
    var_info::Dict{VarId,VarInfo}
end

function LinearIRContext(ctx, lambda_args, return_type)
    ctx = LinearIRContext(ctx.graph, Vector{Any}(), ctx.next_var_id, return_type)
end

function makenode(ctx::LinearIRContext, srcref, head, children...; attrs...)
    makenode(ctx.graph, srcref, head, _node_ids(children...)...; attrs...)
end

function is_valid_body_ir_argument(ex)
    is_valid_ir_argument(ex) && return true
    return false
    # FIXME
    k = kind(ex)
    return k == K"Identifier" && # Arguments are always defined slots
        TODO("vinfo-table stuff")
end

function is_simple_arg(ex)
    k = kind(ex)
    return is_simple_atom(ex) || k == K"Identifier" || k == K"quote" || k == K"inert" ||
           k == K"top" || k == K"core" || k == K"globalref" || k == K"outerref"
end

function is_single_assign_var(ctx::LinearIRContext, ex)
    return true # FIXME
    id = ex.var_id
    # return id in ctx.lambda_args ||
end

function is_const_read_arg(ctx, ex)
    k = kind(ex)
    return is_simple_atom(ex) ||
           single_assign_var(ctx, ex) ||
           k == K"quote" || k == K"inert" || k == K"top" || k == K"core"
end

# evaluate the arguments of a call, creating temporary locations as needed
function compile_args(ctx, args)
    # First check if all the arguments as simple (and therefore side-effect free).
    # Otherwise, we need to use ssa values for all arguments to ensure proper
    # left-to-right evaluation semantics.
    all_simple = all(is_simple_arg, args)
    args_out = Int[]
    for arg in args
        if (all_simple || is_const_read_arg(ctx, arg)) && is_valid_body_ir_argument(arg)
            push!(args_out, arg)
        else
            push!(args_out, emit_assign_tmp(ctx, arg))
        end
    end
    return args_out
end

function emit(ctx::LinearIRContext, ex)
    id = _node_id(ex)
    push!(ctx.code, id)
    return id
end

function emit(ctx::LinearIRContext, srcref, k, args...)
    emit(ctx, makenode(ctx, srcref, k, args...))
end

# Emit computation of ex, assigning the result to an ssavar and returning that
function emit_assign_tmp(ctx::LinearIRContext, ex)
    # TODO: We could replace this with an index into the code array right away?
    id = makenode(ctx, ex, K"SSALabel", var_id=ctx.next_var_id[])
    ctx.next_var_id[] += 1
    emit(ctx, ex, K"=", id, ex)
    return id
end

function emit_return(ctx, srcref, ex)
    if isnothing(ex)
        return
    end
    # TODO: return type handling
    # TODO: exception stack handling
    # returning lambda directly is needed for @generated
    if !(is_valid_ir_argument(ex) || head(ex) == K"lambda")
        ex = emit_assign_tmp(ctx, ex)
    end
    emit(ctx, srcref, K"return", ex)
end

function emit_assignment(ctx, srcref, lhs, rhs)
    if isnothing(rhs)
        if is_valid_ir_rvalue(lhs, rhs)
            emit(ctx, srcref, K"=", lhs, rhs)
        else
            r = emit_assign_tmp(ctx, rhs)
            emit(ctx, srcref, K"=", lhs, r)
        end
    else
        # in unreachable code (such as after return); still emit the assignment
        # so that the structure of those uses is preserved
        # TODO: What should null handling look like?
        emit(ctx, rhs, K"=", lhs, makenode(ctx, srcref, K"Identifier", value=:null))
    end
    nothing
end

# This pass behaves like an interpreter on the given code.
# To perform stateful operations, it calls `emit` to record that something
# needs to be done. In value position, it returns an expression computing
# the needed value.
#
# TODO: is it ok to return `nothing` if we have no value in some sense
function compile(ctx::LinearIRContext, ex, needs_value, in_tail_pos)
    k = kind(ex)
    if k == K"call" || k == K"new"
        # TODO k ∈ splatnew foreigncall cfunction new_opaque_closure cglobal
        args = compile_args(ctx, children(ex))
        callex = makenode(ctx, ex, k, args...)
        if in_tail_pos
            emit_return(ctx, callex)
        elseif needs_value
            callex
        else
            emit(ctx, callex)
            nothing
        end
    elseif k == K"="
        lhs = ex[1]
        # TODO: Handle underscore
        rhs = compile(ctx, ex[2], true, false)
        # TODO look up arg-map for renaming if lhs was reassigned
        if needs_value && !isnothing(rhs)
            r = emit_assign_tmp(ctx, rhs)
            emit(ctx, ex, K"=", lhs, r)
            if in_tail_pos
                emit_return(ctx, ex, r)
            else
                r
            end
        else
            emit_assignment(ctx, ex, lhs, rhs)
        end
    end
end

# flisp: compile-body
function compile_lambda(expansion_ctx, ex)
    lambda_args = Set{VarId}()
    return_type = nothing
    ctx = LinearIRContext(expansion_ctx, lambda_args, return_type)
    compile(ctx, ex[3])
end

