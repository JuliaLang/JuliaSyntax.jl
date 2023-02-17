@testset "parser API" begin
    @testset "parse with String input" begin
        @test parse(Expr, " x ") == :x
        @test JuliaSyntax.remove_linenums!(parseall(Expr, " x ")) == Expr(:toplevel, :x)
        @test parseatom(Expr, " x ") == :x
        # TODO: Fix this situation with trivia here; the brackets are trivia, but
        # must be parsed to discover the atom inside. But in GreenTree we only
        # place trivia as siblings of the leaf node with identifier `x`, not as
        # children.
        @test_broken parseatom(Expr, "(x)") == :x

        # SubString
        @test parse(Expr, SubString("x+y")) == :(x+y)
        @test parse(Expr, SubString("α+x")) == :(α+x)
        @test parseatom(Expr, SubString("x+y",3,3)) == :y

        # Exceptions due to extra trailing syntax
        @test_throws JuliaSyntax.ParseError parseatom(Expr, "x+y")
        @test_throws JuliaSyntax.ParseError parse(Expr, "x+y\nz")

        # ignore_warnings flag
        @test_throws JuliaSyntax.ParseError parse(Expr, "import . .A")
        @test parse(Expr, "import . .A", ignore_warnings=true) == :(import ..A)

        # version selection
        @test_throws JuliaSyntax.ParseError parse(Expr, "[a ;; b]", version=v"1.6")
        @test parse(Expr, "[a ;; b]", version=v"1.7") == Expr(:ncat, 2, :a, :b)

        # filename
        @test JuliaSyntax.parse(Expr, "begin\na\nend", filename="foo.jl", first_line=55) ==
            Expr(:block, LineNumberNode(56, Symbol("foo.jl")), :a)

        # ignore_trivia
        @test parseatom(Expr, " x ", ignore_trivia=true) == :x
        @test_throws JuliaSyntax.ParseError parseatom(Expr, " x ", ignore_trivia=false)
    end

    @testset "IO input" begin
        # IOBuffer
        io = IOBuffer("x+y")
        @test parse!(Expr, io, rule=:statement) == (:(x+y), [])
        @test position(io) == 3
        io = IOBuffer("x+y")
        seek(io, 2)
        @test parse!(Expr, io, rule=:atom) == (:y, [])
        @test position(io) == 3
        # A GenericIOBuffer, not actually IOBuffer
        io = IOBuffer(SubString("x+y"))
        @test parse!(Expr, io, rule=:statement) == (:(x+y), [])
        @test position(io) == 3
        # Another type of GenericIOBuffer
        io = IOBuffer(codeunits("x+y"))
        @test parse!(Expr, io, rule=:statement) == (:(x+y), [])
        @test position(io) == 3
        # IOStream
        mktemp() do path, io
            write(io, "x+y")
            close(io)

            open(path, "r") do io
                @test parse!(Expr, io, rule=:statement) == (:(x+y), [])
                @test position(io) == 3
            end
        end
    end

    @testset "parse with String and index input" begin
        # String
        let
            ex,pos = parseall(Expr, "x+y\nz", 1)
            @test JuliaSyntax.remove_linenums!(ex) == Expr(:toplevel, :(x+y), :z)
            @test pos == 6
        end
        @test parse(Expr, "x+y\nz", 1)     == (:(x+y), 4)
        @test parseatom(Expr, "x+y\nz", 1) == (:x, 2)
        @test parseatom(Expr, "x+y\nz", 5) == (:z, 6)

        # SubString
        @test parse(Expr, SubString("α+x\ny"), 1)  == (:(α+x), 5)
        @test parseatom(Expr, SubString("x+y"), 1) == (:x, 2)
        @test parseatom(Expr, SubString("x+y"), 3) == (:y, 4)
    end

    @testset "error/warning handling" begin
        parseshow(s;kws...) = sprint(show, MIME("text/x.sexpression"), parse(SyntaxNode, s; kws...))
        @test_throws JuliaSyntax.ParseError parseshow("try finally catch ex end")
        @test parseshow("try finally catch ex end", ignore_warnings=true) ==
            "(try_finally_catch (block) false false false (block) ex (block))"
        # ignore_errors
        @test_throws JuliaSyntax.ParseError parseshow("[a; b, c]")
        @test_throws JuliaSyntax.ParseError parseshow("[a; b, c]", ignore_warnings=true)
        @test parseshow("[a; b, c]", ignore_errors=true) == "(vcat a b (error-t) c)"
        # errors in literals
        @test parseshow("\"\\z\"", ignore_errors=true) == "(string (ErrorInvalidEscapeSequence))"
        @test parseshow("'\\z'", ignore_errors=true) == "(char (ErrorInvalidEscapeSequence))"
        @test parseshow("'abc'", ignore_errors=true) == "(char (ErrorOverLongCharacter))"
        @test parseshow("1e1000", ignore_errors=true) == "(ErrorNumericOverflow)"
        @test parseshow("1f1000", ignore_errors=true) == "(ErrorNumericOverflow)"
    end
end
