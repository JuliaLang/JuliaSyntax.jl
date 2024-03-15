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
    return_type::Union{Nothing,NodeId}
    var_info::Dict{VarId,VarInfo}
end

function LinearIRContext(ctx, return_type)
    ctx = LinearIRContext(ctx.graph, SyntaxList(ctx.graph), ctx.next_var_id,
                          return_type, Dict{VarId,VarInfo}())
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

function is_valid_ir_rvalue(lhs, rhs)
    return kind(lhs) == K"SSAValue"  ||
           is_valid_ir_argument(rhs) ||
           (kind(lhs) == K"Identifier" &&
            # FIXME: add: splatnew isdefined invoke cfunction gc_preserve_begin copyast new_opaque_closure globalref outerref
            kind(rhs) in KSet"new the_exception call foreigncall")
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
    tmp = makenode(ctx, ex, K"SSAValue", var_id=ctx.next_var_id[])
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
    # TODO: if !isnothing(ctx.return_type) ...
    emit(ctx, srcref, K"return", ex)
end

function emit_assignment(ctx, srcref, lhs, rhs)
    if !isnothing(rhs)
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
    if k == K"Identifier" || is_literal(k) || k == K"SSAValue" || k == K"quote" || k == K"inert" ||
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


#-------------------------------------------------------------------------------

# Recursively renumber an expression within linear IR
# flisp: renumber-stuff
function _renumber(ctx, ssa_rewrite, arg_rewrite, label_table, ex)
    k = kind(ex)
    if k == K"Identifier"
        id = ex.var_id
        newarg = isnothing(arg_rewrite) ? nothing : get(arg_rewrite, id, nothing)
        if !isnothing(newarg)
            makenode(ctx, ex, newarg[1]; var_id=newarg[2])
        else
            # TODO: Static parameters
            ex
        end
    elseif k == K"outerref" || k == K"meta"
        TODO(ex, "_renumber $k")
    elseif is_literal(k) || is_quoted(k) || k == K"global"
        ex
    elseif k == K"SSAValue"
        makenode(ctx, ex, K"SSAValue"; var_id=ssa_rewrite[ex.var_id])
    elseif k == K"goto" || k == K"enter" || k == K"gotoifnot"
        TODO(ex, "_renumber $k")
    # elseif k == K"lambda"
    #     renumber_lambda(ctx, ex)
    else
        mapchildren(ctx, ex) do e
            _renumber(ctx, ssa_rewrite, arg_rewrite, label_table, e)
        end
        # TODO: foreigncall error check:
        # "ccall function name and library expression cannot reference local variables"
    end
end

# flisp: renumber-lambda, compact-ir
function renumber_body(ctx, input_code, arg_rewrite)
    # Step 1: Remove any assignments to SSA variables, record the indices of labels
    ssa_rewrite = Dict{VarId,VarId}()
    label_table = Dict{String,Int}()
    code = SyntaxList(ctx)
    for ex in input_code
        k = kind(ex)
        ex_out = nothing
        if k == K"=" && kind(ex[1]) == K"SSAValue"
            lhs_id = ex[1].var_id
            if kind(ex[2]) == K"SSAValue"
                # For SSA₁ = SSA₂, record that all uses of SSA₁ should be replaced by SSA₂
                ssa_rewrite[lhs_id] = ssa_rewrite[ex[2].var_id]
            else
                # Otherwise, record which `code` index this SSA value refers to
                ssa_rewrite[lhs_id] = length(code) + 1
                ex_out = ex[2]
            end
        elseif k == K"label"
            label_table[ex.name_val] = length(code) + 1
        else
            ex_out = ex
        end
        if !isnothing(ex_out)
            push!(code, ex_out)
        end
    end
    # Step 2: Translate any SSA uses and labels into indices in the code table
    # Translate function arguments into slot indices
    for i in 1:length(code)
        code[i] = _renumber(ctx, ssa_rewrite, arg_rewrite, label_table, code[i])
    end
    code
end

function renumber_lambda(ctx, lambda_info, code)
    arg_rewrite = Dict{VarId,Tuple{Kind,Int}}()
    # lambda arguments become K"slot"; type parameters become K"static_parameter"
    info = ex.lambda_info
    for (i,arg) in enumerate(info.args)
        arg_rewrite[arg.var_id] = (K"slot",i)
    end
    # TODO: add static_parameter here also
    renumber_body(ctx, code, arg_rewrite)
end

# Our Julia version-independent proxy for CodeInfo ?
# struct LambdaIR
#     args::SyntaxList
#     code::SyntaxList
#     var_info # ::Dict{VarId,VarInfo}
# end

# flisp: compile-body
function compile_body(ctx, ex)
    compile(ctx, ex, true, true)
    # TODO: Fix any gotos
    # TODO: Filter out any newvar nodes where the arg is definitely initialized
end

function compile_lambda(ctx, ex)
    info = ex.lambda_info
    lambda_args = Set{VarId}()
    return_type = nothing
    # TODO: Add assignments for reassigned arguments to body using info.args
    ctx = LinearIRContext(outer_ctx, return_type)
    compile_body(ctx, ex[1])
    # renumber_lambda(ctx, info
    # FIXME: Our replacement for CodeInfo
    #var_info = nothing # FIXME
    #makenode(ctx, ex, K"Value"; value=LambdaIR(info.args, ctx.code, var_info))
end

function compile_toplevel(outer_ctx, ex)
    lambda_args = Set{VarId}()
    return_type = nothing
    ctx = LinearIRContext(outer_ctx, return_type)
    compile_body(ctx, ex)
    arg_rewrite = Dict{VarId,Tuple{Kind,Int}}()
    renumber_body(ctx, ctx.code, arg_rewrite)
    #var_info = nothing # FIXME
    #makenode(ctx, ex, K"Value"; value=LambdaIR(SyntaxList(ctx), ctx.code, var_info))
end

