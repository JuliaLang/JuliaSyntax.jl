using Serialization

@testset "Equality" for T in [Expr, SyntaxNode, JuliaSyntax.GreenNode]
    x = JuliaSyntax.parse(T, "f(x) = x + 2")
    y = JuliaSyntax.parse(T, "f(x) = x + 2")
    z = JuliaSyntax.parse(T, "f(x) = 2 + x")
    @test x == y
    @test x != z
    @test y != z
end

@testset "Hashing" for T in [Expr, SyntaxNode, JuliaSyntax.GreenNode]
    x = hash(JuliaSyntax.parse(T, "f(x) = x + 2"))::UInt
    y = hash(JuliaSyntax.parse(T, "f(x) = x + 2"))::UInt
    z = hash(JuliaSyntax.parse(T, "f(x) = 2 + x"))::UInt
    @test x == y # Correctness
    @test x != z # Collision
    @test y != z # Collision
end

@testset "Serialization" for T in [Expr, SyntaxNode, JuliaSyntax.GreenNode]
    x = JuliaSyntax.parse(T, "f(x) = x + 2")
    f = tempname()
    serialize(f, x)
    y = deserialize(f)
    @test x == y
end
