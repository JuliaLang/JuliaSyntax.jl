JuliaSyntax.include2(Main, "macroexpand_inc.jl")

@testset "macroexpand" begin
    loc = A.LocationMacros.loc()
    @test loc.mod == A.LocationMacros
    @test last(splitpath(loc.file)) ==  "macroexpand_inc.jl"
    @test loc.line == 26
    @test loc.column == 72

    @test A.hygiene_test() == ("x in B", "z in A")

    @test A.old_macro_test(1) == 3
    @test A.old_macro_test(2) == 5

    @test A.macro_calling_macro_test(3) == 27
end
