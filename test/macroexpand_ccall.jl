module CCall

# An implementation of the ccall macro with new macro expansion

@__EXTENSIONS__ new_macros=true

using JuliaSyntax
using JuliaSyntax: SyntaxLiteral, ScopeSpec, MacroExpansionError, is_identifier, numchildren, children

function ccall_macro_parse(ex)
    if kind(ex) != K"::"
        throw(MacroExpansionError(ex, "Expected a return type annotation like `::T`", after=true))
    end
    rettype = ex[2]
    call = ex[1]
    if kind(call) != K"call"
        throw(MacroExpansionError(call, "Expected function call syntax `f()`"))
    end

    # get the function symbols
    func = let f = call[1], kf = kind(f)
        if kf == K"."
            (f[2], f[1])
        elseif kf == K"$"
            f
        elseif is_identifier(kf)
            SyntaxLiteral(K"inert", f, [f])
        else
            throw(MacroExpansionError(f,
                "Function name must be a symbol like `foo`, a library and function name like `libc.printf` or an interpolated function pointer like `\$ptr`"))
        end
    end

    varargs = nothing

    # collect args and types
    args = SyntaxLiteral[]
    types = SyntaxLiteral[]

    function pusharg!(arg)
        if kind(arg) != K"::"
            throw(MacroExpansionError(arg, "argument needs a type annotation like `::T`", after=true))
        end
        push!(args, arg[1])
        push!(types, arg[2])
    end

    varargs = nothing
    num_varargs = 0
    for e in Iterators.drop(children(call), 1) # FIXME this is ugly ...
        if kind(e) == K"parameters"
            num_varargs == 0 || throw(MacroExpansionError(e, "Multiple parameter blocks not allowed"))
            num_varargs = numchildren(e)
            num_varargs > 0 || throw(MacroExpansionError(e, "C ABI prohibits vararg without one required argument"))
            varargs = children(e)
        else
            pusharg!(e)
        end
    end
    if !isnothing(varargs)
        for e in varargs
            pusharg!(e)
        end
    end

    return func, rettype, types, args, num_varargs
end

function ccall_macro_lower(ex, convention, func, rettype, types, args, num_varargs)
    statements = SyntaxLiteral[]
    if kind(func) == K"$"
        check = quote
            func = $(func[1])
            if !isa(func, Ptr{Cvoid})
                name = :($(func[1]))
                throw(ArgumentError("interpolated function `$name` was not a Ptr{Cvoid}, but $(typeof(func))"))
            end
        end
        func = check[1][1]
        push!(statements, check)
    end

    roots = SyntaxLiteral[]
    cargs = SyntaxLiteral[]
    for (i, (type, arg)) in enumerate(zip(types, args))
        # FIXME: Need utility function for identifiers, which are no longer
        # plain symbols? Or can we upgrade interpolation code to detect this
        # case and attribute them to the interpolation location?
        #     argi = @Identifier("arg$i")
        #     argi = Identifier(@__MODULE__, "arg$i")
        # Which means Symbol("arg$i") with the current module ??
        argi = Symbol("arg$i")
        # TODO: Can we use SSAValue here? Lowering can do this ... but
        # presumably that implies some invariants?
        push!(statements, :(local $argi = Base.cconvert($type, $arg)))
        push!(roots, :($argi))
        push!(cargs, :(Base.unsafe_convert($type, $argi)))
    end
    push!(statements, SyntaxLiteral(K"foreigncall", 
                                    ex,
                                    SyntaxLiteral[func,
                                     rettype,
                                     :(Core.svec($(types...))),
                                     :($num_varargs),
                                     # TODO: Gosh constructing this quoted
                                     # symbol was too hard to get correct. We
                                     # need something better.
                                     SyntaxLiteral(K"inert", ex, [:($convention)]),
                                     cargs...,
                                     roots...
                                    ]))
    quote
        $(statements...)
    end
end

macro ccall(ex)
    ccall_macro_lower(ex, Symbol("ccall"), ccall_macro_parse(ex)...)
end

# @ccall printf("%s = %d\n"::Cstring; "var"::Cstring, 42::Cint)::Cint
# nothing

end

