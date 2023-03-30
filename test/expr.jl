@testset "Expr conversion" begin
    @testset "Quote nodes" begin
        @test parseatom(Expr, ":(a)") == QuoteNode(:a)
        @test parseatom(Expr, ":(:a)") == Expr(:quote, QuoteNode(:a))
        @test parseatom(Expr, ":(1+2)") == Expr(:quote, Expr(:call, :+, 1, 2))
        # Compatibility hack for VERSION >= v"1.4"
        # https://github.com/JuliaLang/julia/pull/34077
        @test parseatom(Expr, ":true") == Expr(:quote, true)
    end

    @testset "Line numbers" begin
        @testset "Blocks" begin
            @test parsex(Expr, "begin a\nb\n\nc\nend") ==
                Expr(:block,
                     LineNumberNode(1),
                     :a,
                     LineNumberNode(2),
                     :b,
                     LineNumberNode(4),
                     :c,
                )
            @test parsex(Expr, "begin end") ==
                Expr(:block,
                     LineNumberNode(1)
                )

            @test parseall(Expr, "a\n\nb") ==
                Expr(:toplevel,
                     LineNumberNode(1),
                     :a,
                     LineNumberNode(3),
                     :b,
                )

            @test parsex(Expr, "module A\n\nbody\nend") ==
                Expr(:module,
                     true,
                     :A,
                     Expr(:block,
                          LineNumberNode(1),
                          LineNumberNode(3),
                          :body,
                     ),
                )
        end

        @testset "Function definition lines" begin
            @test parsex(Expr, "function f()\na\n\nb\nend") ==
                Expr(:function,
                     Expr(:call, :f),
                     Expr(:block,
                         LineNumberNode(1),
                         LineNumberNode(2),
                         :a,
                         LineNumberNode(4),
                         :b,
                     )
                )
            @test parsex(Expr, "f() = 1") ==
                Expr(:(=),
                     Expr(:call, :f),
                     Expr(:block,
                          LineNumberNode(1),
                          1
                     )
                )

            # function/macro without methods
            @test parsex(Expr, "function f end") ==
                Expr(:function, :f)
            @test parsex(Expr, "macro f end") ==
                Expr(:macro, :f)
        end

        @testset "elseif" begin
            @test parsex(Expr, "if a\nb\nelseif c\n d\nend") ==
                Expr(:if,
                     :a,
                     Expr(:block,
                          LineNumberNode(2),
                          :b),
                     Expr(:elseif,
                          Expr(:block,
                               LineNumberNode(3),  # Line number for elseif condition
                               :c),
                          Expr(:block,
                               LineNumberNode(4),
                               :d),
                     )
                )
        end

        @testset "No line numbers in for/let bindings" begin
            @test parsex(Expr, "for i=is, j=js\nbody\nend") ==
                Expr(:for,
                     Expr(:block,
                         Expr(:(=), :i, :is),
                         Expr(:(=), :j, :js),
                     ),
                     Expr(:block,
                         LineNumberNode(2),
                         :body
                     )
                )
            @test parsex(Expr, "let i=is, j=js\nbody\nend") ==
                Expr(:let,
                     Expr(:block,
                         Expr(:(=), :i, :is),
                         Expr(:(=), :j, :js),
                     ),
                     Expr(:block,
                         LineNumberNode(2),
                         :body
                     )
                )
        end
    end

    @testset "Short form function line numbers" begin
        # A block is added to hold the line number node
        @test parsex(Expr, "f() = xs") ==
            Expr(:(=),
                 Expr(:call, :f),
                 Expr(:block,
                      LineNumberNode(1),
                      :xs))
        # flisp parser quirk: In a for loop the block is not added, despite
        # this defining a short-form function.
        @test parsex(Expr, "for f() = xs\nend") ==
            Expr(:for,
                 Expr(:(=), Expr(:call, :f), :xs),
                 Expr(:block,
                      LineNumberNode(1)
                     ))
    end

    @testset "Long form anonymous functions" begin
        @test parsex(Expr, "function (xs...)\nbody end") ==
            Expr(:function,
                 Expr(:..., :xs),
                 Expr(:block,
                      LineNumberNode(1),
                      LineNumberNode(2),
                      :body))
    end

    @testset "String conversions" begin
        # String unwrapping / wrapping
        @test parsex(Expr, "\"str\"") == "str"
        @test parsex(Expr, "\"\$(\"str\")\"") ==
            Expr(:string, Expr(:string, "str"))
        # Concatenation of string chunks in triple quoted cases
        @test parsex(Expr, "```\n  a\n  b```") ==
            Expr(:macrocall, GlobalRef(Core, Symbol("@cmd")), LineNumberNode(1),
                 "a\nb")
        @test parsex(Expr, "\"\"\"\n  a\n  \$x\n  b\n  c\"\"\"") ==
            Expr(:string, "a\n", :x, "\nb\nc")
    end

    @testset "Char conversions" begin
        @test parsex(Expr, "'a'") == 'a'
        @test parsex(Expr, "'α'") == 'α'
        @test parsex(Expr, "'\\xce\\xb1'") == 'α'
    end

    @testset "do block conversion" begin
        @test parsex(Expr, "f(x) do y\n body end") ==
            Expr(:do, Expr(:call, :f, :x),
                 Expr(:->, Expr(:tuple, :y),
                      Expr(:block,
                           LineNumberNode(2),
                           :body)))
    end

    @testset "= to Expr(:kw) conversion" begin
        # Call
        @test parsex(Expr, "f(a=1)") ==
            Expr(:call, :f, Expr(:kw, :a, 1))
        @test parsex(Expr, "f(; b=2)") ==
            Expr(:call, :f, Expr(:parameters, Expr(:kw, :b, 2)))
        @test parsex(Expr, "f(a=1; b=2)") ==
            Expr(:call, :f, Expr(:parameters, Expr(:kw, :b, 2)), Expr(:kw, :a, 1))

        # Infix call = is not :kw
        @test parsex(Expr, "(x=1) != 2") ==
            Expr(:call, :!=, Expr(:(=), :x, 1), 2)

        # Dotcall
        @test parsex(Expr, "f.(a=1; b=2)") ==
            Expr(:., :f, Expr(:tuple,
                              Expr(:parameters, Expr(:kw, :b, 2)),
                              Expr(:kw, :a, 1)))

        # Named tuples
        @test parsex(Expr, "(a=1,)") ==
            Expr(:tuple, Expr(:(=), :a, 1))
        @test parsex(Expr, "(a=1,; b=2)") ==
            Expr(:tuple, Expr(:parameters, Expr(:kw, :b, 2)), Expr(:(=), :a, 1))
        @test parsex(Expr, "(a=1,; b=2; c=3)") ==
            Expr(:tuple,
                 Expr(:parameters,
                      Expr(:parameters, Expr(:kw, :c, 3)),
                      Expr(:kw, :b, 2)),
                 Expr(:(=), :a, 1))

        # ref
        @test parsex(Expr, "x[i=j]") ==
            Expr(:ref, :x, Expr(:kw, :i, :j))
        @test parsex(Expr, "(i=j)[x]") ==
            Expr(:ref, Expr(:(=), :i, :j), :x)
        @test parsex(Expr, "x[a, b; i=j]") ==
            Expr(:ref, :x, Expr(:parameters, Expr(:(=), :i, :j)), :a, :b)
        # curly
        @test parsex(Expr, "(i=j){x}") ==
            Expr(:curly, Expr(:(=), :i, :j), :x)
        @test parsex(Expr, "x{a, b; i=j}") ==
            Expr(:curly, :x, Expr(:parameters, Expr(:(=), :i, :j)), :a, :b)

        # vect
        @test parsex(Expr, "[a=1,; b=2]") ==
            Expr(:vect,
                 Expr(:parameters, Expr(:(=), :b, 2)),
                 Expr(:(=), :a, 1))
        # braces
        @test parsex(Expr, "{a=1,; b=2}") ==
            Expr(:braces,
                 Expr(:parameters, Expr(:(=), :b, 2)),
                 Expr(:(=), :a, 1))

        # dotted = is not :kw
        @test parsex(Expr, "f(a .= 1)") ==
            Expr(:call, :f, Expr(:.=, :a, 1))

        # = inside parens in calls and tuples
        # (TODO: we should warn for these cases.)
        @test parsex(Expr, "f(((a = 1)))") ==
            Expr(:call, :f, Expr(:kw, :a, 1))
        @test parsex(Expr, "(((a = 1)),)") ==
            Expr(:tuple, Expr(:(=), :a, 1))
        @test parsex(Expr, "(;((a = 1)),)") ==
            Expr(:tuple, Expr(:parameters, Expr(:kw, :a, 1)))
    end

    @testset "dotcall" begin
        @test parsex(Expr, "f.(x,y)") == Expr(:., :f, Expr(:tuple, :x, :y))
        @test parsex(Expr, "f.(x=1)") == Expr(:., :f, Expr(:tuple, Expr(:kw, :x, 1)))
        @test parsex(Expr, "x .+ y")  == Expr(:call, Symbol(".+"), :x, :y)
        @test parsex(Expr, "(x=1) .+ y") == Expr(:call, Symbol(".+"), Expr(:(=), :x, 1), :y)
        @test parsex(Expr, "a .< b .< c") == Expr(:comparison, :a, Symbol(".<"),
                                                 :b, Symbol(".<"), :c)
        @test parsex(Expr, ".*(x)")  == Expr(:call, Symbol(".*"), :x)
        @test parsex(Expr, ".+(x)")  == Expr(:call, Symbol(".+"), :x)
        @test parsex(Expr, ".+x")    == Expr(:call, Symbol(".+"), :x)
    end

    @testset "where" begin
        @test parsex(Expr, "A where {X, Y; Z}") == Expr(:where, :A, Expr(:parameters, :Z), :X, :Y)
    end

    @testset "macrocall" begin
        # line numbers
        @test parsex(Expr, "@m\n") == Expr(:macrocall, Symbol("@m"), LineNumberNode(1))
        @test parsex(Expr, "\n@m") == Expr(:macrocall, Symbol("@m"), LineNumberNode(2))
        # parameters
        @test parsex(Expr, "@m(x; a)") == Expr(:macrocall, Symbol("@m"), LineNumberNode(1),
                                              Expr(:parameters, :a), :x)
        @test parsex(Expr, "@m(a=1; b=2)") == Expr(:macrocall, Symbol("@m"), LineNumberNode(1),
                                                  Expr(:parameters, Expr(:kw, :b, 2)), Expr(:(=), :a, 1))
        # @__dot__
        @test parsex(Expr, "@.") == Expr(:macrocall, Symbol("@__dot__"), LineNumberNode(1))
        @test parsex(Expr, "using A: @.") == Expr(:using, Expr(Symbol(":"), Expr(:., :A), Expr(:., Symbol("@__dot__"))))
    end

    @testset "try" begin
        @test parsex(Expr, "try x catch e; y end") ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 :e,
                 Expr(:block, LineNumberNode(1), :y))
        @test parsex(Expr, "try x finally y end") ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 false,
                 false,
                 Expr(:block, LineNumberNode(1), :y))
        @test parsex(Expr, "try x catch e; y finally z end") ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 :e,
                 Expr(:block, LineNumberNode(1), :y),
                 Expr(:block, LineNumberNode(1), :z))
        @test parsex(Expr, "try x catch e; y else z end", version=v"1.8") ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 :e,
                 Expr(:block, LineNumberNode(1), :y),
                 false,
                 Expr(:block, LineNumberNode(1), :z))
        @test parsex(Expr, "try x catch e; y else z finally w end", version=v"1.8") ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 :e,
                 Expr(:block, LineNumberNode(1), :y),
                 Expr(:block, LineNumberNode(1), :w),
                 Expr(:block, LineNumberNode(1), :z))
        # finally before catch
        @test parsex(Expr, "try x finally y catch e z end", ignore_warnings=true) ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 :e,
                 Expr(:block, LineNumberNode(1), :z),
                 Expr(:block, LineNumberNode(1), :y))
        # empty recovery
        @test parsex(Expr, "try x end", ignore_errors=true) ==
            Expr(:try,
                 Expr(:block, LineNumberNode(1), :x),
                 false, false,
                 Expr(:block, Expr(:error)))
    end

    @testset "juxtapose" begin
        @test parsex(Expr, "2x") == Expr(:call, :*, 2, :x)
        @test parsex(Expr, "(2)(3)x") == Expr(:call, :*, 2, 3, :x)
    end

    @testset "Core.@doc" begin
        @test parsex(Expr, "\"x\" f") ==
            Expr(:macrocall, GlobalRef(Core, Symbol("@doc")), LineNumberNode(1), "x", :f)
        @test parsex(Expr, "\n\"x\" f") ==
            Expr(:macrocall, GlobalRef(Core, Symbol("@doc")), LineNumberNode(2), "x", :f)
    end

    @testset "return" begin
        @test parsex(Expr, "return x") == Expr(:return, :x)
        @test parsex(Expr, "return")  == Expr(:return, nothing)
    end

    @testset "struct" begin
        @test parsex(Expr, "struct A end") ==
            Expr(:struct, false, :A, Expr(:block, LineNumberNode(1)))
        @test parsex(Expr, "mutable struct A end") ==
            Expr(:struct, true, :A, Expr(:block, LineNumberNode(1)))
    end

    @testset "module" begin
        @test parsex(Expr, "module A end") ==
            Expr(:module, true,  :A, Expr(:block, LineNumberNode(1), LineNumberNode(1)))
        @test parsex(Expr, "baremodule A end") ==
            Expr(:module, false, :A, Expr(:block, LineNumberNode(1), LineNumberNode(1)))
    end


    @testset "errors" begin
        @test parsex(Expr, "--", ignore_errors=true) ==
            Expr(:error, "invalid operator: `--`")
        @test parseall(Expr, "a b", ignore_errors=true) ==
            Expr(:toplevel, LineNumberNode(1), :a,
                 LineNumberNode(1), Expr(:error, :b))
        @test parsex(Expr, "(x", ignore_errors=true) ==
            Expr(:block, :x, Expr(:error))
    end

    @testset "import" begin
        @test parsex(Expr, "import A.(:b).:c: x.:z", ignore_warnings=true) ==
            Expr(:import, Expr(Symbol(":"), Expr(:., :A, :b, :c), Expr(:., :x, :z)))
        # Stupid parens and quotes in import paths
        @test parsex(Expr, "import A.:+", ignore_warnings=true) ==
            Expr(:import, Expr(:., :A, :+))
        @test parsex(Expr, "import A.(:+)", ignore_warnings=true) ==
            Expr(:import, Expr(:., :A, :+))
        @test parsex(Expr, "import A.:(+)", ignore_warnings=true) ==
            Expr(:import, Expr(:., :A, :+))
        @test parsex(Expr, "import A.:(+) as y", ignore_warnings=true, version=v"1.6") ==
            Expr(:import, Expr(:as, Expr(:., :A, :+), :y))
    end
end
