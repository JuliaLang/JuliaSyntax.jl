module A

@__EXTENSIONS__ new_macros=true

module LocationMacros
    using JuliaSyntax

    macro __MODULE__()
        __context__.module
    end

    macro __FILE__()
        JuliaSyntax.filename(__context__.macroname)
    end

    macro __LINE__()
        JuliaSyntax.source_line(__context__.macroname)
    end

    macro __COLUMN__()
        c = JuliaSyntax.source_location(__context__.macroname)[2]
        return JuliaSyntax.kind(__context__.macroname) == K"MacroName" ? c - 1 : c
    end

    function loc()
        (mod=@__MODULE__(), file=@__FILE__(), line=@__LINE__(), column=@__COLUMN__())
    end
end

using JuliaSyntax
using JuliaSyntax: valueof, MacroExpansionError, emit_diagnostic

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

macro error_test(body)
    if kind(body) == K"tuple"
        error("\"Unexpected\" error")
    elseif kind(body) != K"block"
        throw(MacroExpansionError(body, "Expected a `begin ... end` block"))
    end

    # A way to do more complicated diagnostics:
    diagnostics = JuliaSyntax.Diagnostics()
    for e in body
        if kind(e) != K"call"
            emit_diagnostic(diagnostics, e, error="Expected call")
        end
    end
    if !isempty(diagnostics)
        throw(MacroExpansionError(nothing, diagnostics))
    end
end

function macro_calling_macro_test(x)
    @smallpow_wrapped x^3
end

function old_macro_test(x)
    @evalpoly x 1 2
end

function bad_macro_invocation(case)
    if case == 1
        :(@error_test (1,2))
    elseif case == 2
        :(@error_test begin
            a+b
            [1,2,3]
            f(x,y)
            z
        end)
    else
        :(@error_test function foo()
        do_stuff
        end)
    end
end

macro letx(arg)
    quote
        let x = 42
            $arg, x
        end
    end
end

let x = 84
    y = @letx x
    #@info "" y
end

end

@testset "macroexpand" begin
    loc = A.LocationMacros.loc()
    @test loc.mod == A.LocationMacros
    @test last(splitpath(loc.file)) ==  "macroexpand.jl"
    @test loc.line == 26
    @test loc.column == 72

    @test A.hygiene_test() == ("x in B", "z in A", "in @g")

    @test A.old_macro_test(1) == 3
    @test A.old_macro_test(2) == 5

    @test A.macro_calling_macro_test(3) == 27

    @test_throws JuliaSyntax.MacroExpansionError A.eval(A.bad_macro_invocation(1))
    @test_throws JuliaSyntax.MacroExpansionError A.eval(A.bad_macro_invocation(2))
    @test_throws JuliaSyntax.MacroExpansionError A.eval(A.bad_macro_invocation(3))
end
