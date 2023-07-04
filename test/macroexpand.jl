JuliaSyntax.include_string(Main, raw"""

module A

module B

x = "x in B"

macro f(y)
   quote
       (x, $y)
   end
end

end

import .B: @f

z = "z in A"

function h()
   @f z
end

end

""", filename="bar.jl")

@testset "macroexpand" begin
    @test A.h() == ("x in B", "z in A")
end
