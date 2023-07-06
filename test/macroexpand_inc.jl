module A

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

module B
    x = "x in B"

    macro f(y)
        quote
            (x, $y)
        end
    end
end

z = "z in A"

function hygiene_test()
    B.@f z
end

function old_macro_test(x)
    @evalpoly x 1 2
end

end
