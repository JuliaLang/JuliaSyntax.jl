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
struct LinearIRContext{GraphType} <: AbstractLoweringContext
    graph::GraphType
    code::SyntaxList{GraphType, Vector{NodeId}}
    next_var_id::Ref{Int}
    lambda_args::Set{VarId}
    return_type::Union{Nothing,NodeId}
    var_info::Dict{VarId,VarInfo}
end

function LinearIRContext(ctx, lambda_args, return_type)
    ctx = LinearIRContext(ctx.graph, SyntaxList(ctx.graph), ctx.next_var_id,
                          lambda_args, return_type, Dict{VarId,VarInfo}())
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
    args_out = SyntaxList(ctx)
    for arg in args
        arg_val = compile(ctx, arg, true, false)
        if (all_simple || is_const_read_arg(ctx, arg_val)) && is_valid_body_ir_argument(arg_val)
            push!(args_out, arg_val)
        else
            push!(args_out, emit_assign_tmp(ctx, arg_val))
        end
    end
    return args_out
end

function emit(ctx::LinearIRContext, ex)
    push!(ctx.code, ex)
    return ex
end

function emit(ctx::LinearIRContext, srcref, k, args...)
    emit(ctx, makenode(ctx, srcref, k, args...))
end

# Emit computation of ex, assigning the result to an ssavar and returning that
function emit_assign_tmp(ctx::LinearIRContext, ex)
    # TODO: We could replace this with an index into the code array right away?
    tmp = makenode(ctx, ex, K"SSALabel", var_id=ctx.next_var_id[])
    ctx.next_var_id[] += 1
    emit(ctx, ex, K"=", tmp, ex)
    return tmp
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
        emit(ctx, rhs, K"=", lhs, nothing_(ctx, srcref))
        nothing
    end
end

# This pass behaves like an interpreter on the given code.
# To perform stateful operations, it calls `emit` to record that something
# needs to be done. In value position, it returns an expression computing
# the needed value.
#
# TODO: is it ok to return `nothing` if we have no value in some sense
function compile(ctx::LinearIRContext, ex, needs_value, in_tail_pos)
    k = kind(ex)
    if k == K"Identifier" || is_literal(k) || k == K"SSALabel" || k == K"quote" || k == K"inert" ||
            k == K"top" || k == K"core"
        # TODO: other kinds: copyast the_exception $ globalref outerref thismodule cdecl stdcall fastcall thiscall llvmcall
        if in_tail_pos
            emit_return(ctx, ex, ex)
        elseif needs_value
            if is_placeholder(ex)
                # TODO: ensure outterref, globalref work here
                throw(LoweringError(ex, "all-underscore identifiers are write-only and their values cannot be used in expressions"))
            end
            ex
        else
            if k == K"Identifier"
                emit(ctx, ex) # keep symbols for undefined-var checking
            end
            nothing
        end
    elseif k == K"call"
        # TODO k ∈ splatnew foreigncall cfunction new_opaque_closure cglobal
        args = compile_args(ctx, children(ex))
        callex = makenode(ctx, ex, k, args)
        if in_tail_pos
            emit_return(ctx, ex, callex)
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
    elseif k == K"block"
        nc = numchildren(ex)
        for i in 1:nc
            islast = i == nc
            compile(ctx, ex[i], islast && needs_value, islast && in_tail_pos)
        end
    elseif k == K"return"
        compile(ctx, ex[1], true, true)
        nothing
    elseif k == K"method"
        TODO(ex, "linearize method")
    elseif k == K"lambda"
        lam = compile_lambda(ctx, ex)
        if in_tail_pos
            emit_return(ctx, ex, lam)
        elseif needs_value
            lam
        else
            emit(ctx, lam)
        end
    elseif k == K"global"
        if needs_value
            throw(LoweringError(ex, "misplaced `global` declaration"))
        end
        emit(ctx, ex)
        nothing
    elseif k == K"local_def" || k == K"local"
        nothing
    else
        throw(LoweringError(ex, "Invalid syntax"))
    end
end

# flisp: compile-body
function compile_body(ctx, ex)
    # TODO: Generate assignments to newly named mutable vars, for every argument
    # which is reassigned.
    compile(ctx, ex, true, true)
    # TODO: Fix any gotos
    # TODO: Filter out any newvar nodes where the arg is definitely initialized
    # TODO: Add assignments for reassigned arguments to body
end

function compile_lambda(ctx, ex)
    TODO(ex, "compile_lambda args")
    lambda_args = Set{VarId}()
    return_type = nothing
    ctx = LinearIRContext(outer_ctx, lambda_args, return_type)
    compile_body(ctx, ex[3])
end

function compile_toplevel(outer_ctx, ex)
    lambda_args = Set{VarId}()
    return_type = nothing
    ctx = LinearIRContext(outer_ctx, lambda_args, return_type)
    compile_body(ctx, ex)
    ctx
end

