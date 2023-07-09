module A

@__EXTENSIONS__ new_macros=true

module LocationMacros
    using JuliaSyntax

    macro __MODULE__()
        __module__
    end

    macro __FILE__()
        JuliaSyntax.filename(__macroname__)
    end

    macro __LINE__()
        JuliaSyntax.source_line(__macroname__)
    end

    macro __COLUMN__()
        c = JuliaSyntax.source_location(__macroname__)[2]
        return JuliaSyntax.kind(__macroname__) == K"MacroName" ? c - 1 : c
    end

    function loc()
        (mod=@__MODULE__(), file=@__FILE__(), line=@__LINE__(), column=@__COLUMN__())
    end
end

using JuliaSyntax
using JuliaSyntax: valueof

module B
    x = "x in B"

    macro g()
        "in @g"
    end

    macro f(y)
        quote
            (x, $y, @g)
        end
    end
end

z = "z in A"

function hygiene_test()
    B.@f z
end

macro smallpow(ex)
    @assert kind(ex) == K"call"
    @assert JuliaSyntax.is_infix_op_call(ex)
    @assert valueof(ex[2]) == :^
    N = valueof(ex[3])
    @assert N isa Integer
    e = ex[1]
    for i = 2:N
        e = :($e * $(ex[1]))
    end
    return e
end

macro smallpow_wrapped(ex)
    quote
        @smallpow $ex
    end
end

function macro_calling_macro_test(x)
    @smallpow_wrapped x^3
end

function old_macro_test(x)
    @evalpoly x 1 2
end

end
