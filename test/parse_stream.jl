# Prototype ParseStream interface
#
# Here we test the ParseStream interface, by taking input code and checking
# that the correct sequence of emit() and bump() produces a valid parse tree.

using JuliaSyntax: ParseStream,
    peek, peek_token,
    bump, bump_trivia, bump_invisible,
    emit, emit_diagnostic, TRIVIA_FLAG, INFIX_FLAG,
    ParseStreamPosition, first_child_position, last_child_position,
    parsestmt

# Here we manually issue parse events in the order the Julia parser would issue
# them
@testset "ParseStream" begin
    code = """
    for i = 1:10
        xx[i] + 2
        # hi
        yy
    end
    """

    st = ParseStream(code)

    p1 = position(st)
        @test peek(st) == K"for"
        bump(st, TRIVIA_FLAG)
        p2 = position(st)
            @test peek(st) == K"Identifier"    # 'i'
            bump(st)
            @test peek(st) == K"="
            bump(st, TRIVIA_FLAG)
            p3 = position(st)
                @test peek(st) == K"Integer"   # 1
                bump(st)
                @test peek(st) == K":"
                bump(st) # :
                @test peek(st) == K"Integer"   # 10
                bump(st) # 10
            emit(st, p3, K"call", INFIX_FLAG)
        emit(st, p2, K"=")
        @test peek(st) == K"NewlineWs"
        bump(st, TRIVIA_FLAG)
        p4 = position(st)
            p5 = position(st) # [call]
                p6 = position(st) # [ref]
                    @test peek(st) == K"Identifier" # 'xx'
                    bump(st)
                    @test peek(st) == K"["
                    bump(st, TRIVIA_FLAG)
                    @test peek(st) == K"Identifier" # 'i'
                    bump(st)
                    @test peek(st) == K"]"
                    bump(st, TRIVIA_FLAG)
                emit(st, p6, K"ref")
                @test peek(st) == K"+"
                bump(st)
                @test peek(st) == K"Integer"        # 2
                bump(st)
            emit(st, p5, K"call", INFIX_FLAG)
            @test peek(st) == K"NewlineWs"
            bump(st, TRIVIA_FLAG)
            @test peek(st) == K"NewlineWs"
            bump(st, TRIVIA_FLAG)
            @test peek(st) == K"Identifier" # 'yy'
            bump(st)
        emit(st, p4, K"block")
        @test peek(st) == K"NewlineWs"
        bump(st, TRIVIA_FLAG)
        bump(st, TRIVIA_FLAG) # end
    emit(st, p1, K"for")
    @test peek(st) == K"NewlineWs"
    bump(st, TRIVIA_FLAG)
    emit(st, p1, K"toplevel")

    @test build_tree(GreenNode, st) isa JuliaSyntax.GreenNode
end

@testset "ParseStream constructors" begin
    @testset "Byte buffer inputs" begin
        # Vector{UInt8}
        let
            st = ParseStream(Vector{UInt8}("x+y"))
            bump(st)
            @test build_tree(Expr, st) == :x
            @test JuliaSyntax.last_byte(st) == 1
        end
        let
            st = ParseStream(Vector{UInt8}("x+y"), 3)
            bump(st)
            @test build_tree(Expr, st) == :y
            @test JuliaSyntax.last_byte(st) == 3
        end
        # Ptr{UInt8}, len
        code = "x+y"
        GC.@preserve code begin
            let
                st = ParseStream(pointer(code), 3)
                bump(st)
                @test build_tree(Expr, st) == :x
                @test JuliaSyntax.last_byte(st) == 1
            end
        end
    end
end

@testset "ParseStream tree traversal" begin
    # NB: ParseStreamPosition.token_index includes an initial sentinel token so
    # indices here are one more than "might be expected".
    st = parse_sexpr("((a b) c)")
    child1_pos = first_child_position(st, position(st))
    @test child1_pos == ParseStreamPosition(7, 1)
    @test first_child_position(st, child1_pos) == ParseStreamPosition(4, 0)
    @test last_child_position(st, position(st)) == ParseStreamPosition(9, 0)
    @test last_child_position(st, child1_pos) == ParseStreamPosition(6, 0)

    st = parse_sexpr("( (a b) c)")
    child1_pos = first_child_position(st, position(st))
    @test child1_pos == ParseStreamPosition(8, 1)
    @test first_child_position(st, child1_pos) == ParseStreamPosition(5, 0)
    @test last_child_position(st, position(st)) == ParseStreamPosition(10, 0)
    @test last_child_position(st, child1_pos) == ParseStreamPosition(7, 0)

    st = parse_sexpr("(a (b c))")
    @test first_child_position(st, position(st)) == ParseStreamPosition(3, 0)
    child2_pos = last_child_position(st, position(st))
    @test child2_pos == ParseStreamPosition(9, 1)
    @test first_child_position(st, child2_pos) == ParseStreamPosition(6, 0)
    @test last_child_position(st, child2_pos) == ParseStreamPosition(8, 0)

    st = parse_sexpr("( a (b c))")
    @test first_child_position(st, position(st)) == ParseStreamPosition(4, 0)
    child2_pos = last_child_position(st, position(st))
    @test child2_pos == ParseStreamPosition(10, 1)
    @test first_child_position(st, child2_pos) == ParseStreamPosition(7, 0)
    @test last_child_position(st, child2_pos) == ParseStreamPosition(9, 0)

    st = parse_sexpr("a (b c)")
    @test first_child_position(st, position(st)) == ParseStreamPosition(5, 0)
    @test last_child_position(st, position(st)) == ParseStreamPosition(7, 0)

    st = parse_sexpr("(a) (b c)")
    @test first_child_position(st, position(st)) == ParseStreamPosition(7, 0)
    @test last_child_position(st, position(st)) == ParseStreamPosition(9, 0)

    st = parse_sexpr("(() ())")
    @test first_child_position(st, position(st)) == ParseStreamPosition(4, 1)
    @test last_child_position(st, position(st)) == ParseStreamPosition(7, 2)
end

# This is coppied from InlineStrings.jl instead of depending
# on InlineStrings for compat with Julia 1.2 and earlier:
primitive type String3 <: AbstractString 4*8 end
Base.ncodeunits(x::String3) = Int(Base.trunc_int(UInt8, x))
function Base.codeunit(x::T, i::Int) where {T <: String3}
    @boundscheck checkbounds(Bool, x, i) || throw(BoundsError(x, i))
    return Base.trunc_int(UInt8, Base.lshr_int(x, 8 * (sizeof(T) - i)))
end
function Base.String(x::T) where {T <: String3}
    len = ncodeunits(x)
    out = Base._string_n(len)
    ref = Ref{T}(_bswap(x))
    GC.@preserve ref out begin
        ptr = convert(Ptr{UInt8}, Base.unsafe_convert(Ptr{T}, ref))
        unsafe_copyto!(pointer(out), ptr, len)
    end
    return out
end
function Base.isvalid(x::String3, i::Int)
    @boundscheck checkbounds(Bool, x, i) || throw(BoundsError(x, i))
    return @inbounds thisind(x, i) == i
end
function Base.thisind(s::String3, i::Int)
    i == 0 && return 0
    n = ncodeunits(s)
    i == n + 1 && return i
    @boundscheck Base.between(i, 1, n) || throw(BoundsError(s, i))
    @inbounds b = codeunit(s, i)
    (b & 0xc0 == 0x80) & (i-1 > 0) || return i
    @inbounds b = codeunit(s, i-1)
    Base.between(b, 0b11000000, 0b11110111) && return i-1
    (b & 0xc0 == 0x80) & (i-2 > 0) || return i
    @inbounds b = codeunit(s, i-2)
    Base.between(b, 0b11100000, 0b11110111) && return i-2
    (b & 0xc0 == 0x80) & (i-3 > 0) || return i
    @inbounds b = codeunit(s, i-3)
    Base.between(b, 0b11110000, 0b11110111) && return i-3
    return i
end
Base.@propagate_inbounds function Base.iterate(s::String3, i::Int=firstindex(s))
    (i % UInt) - 1 < ncodeunits(s) || return nothing
    b = @inbounds codeunit(s, i)
    u = UInt32(b) << 24
    Base.between(b, 0x80, 0xf7) || return reinterpret(Char, u), i+1
    return iterate_continued(s, i, u)
end
function iterate_continued(s::String3, i::Int, u::UInt32)
    u < 0xc0000000 && (i += 1; @goto ret)
    n = ncodeunits(s)
    # first continuation byte
    (i += 1) > n && @goto ret
    @inbounds b = codeunit(s, i)
    b & 0xc0 == 0x80 || @goto ret
    u |= UInt32(b) << 16
    # second continuation byte
    ((i += 1) > n) | (u < 0xe0000000) && @goto ret
    @inbounds b = codeunit(s, i)
    b & 0xc0 == 0x80 || @goto ret
    u |= UInt32(b) << 8
    # third continuation byte
    ((i += 1) > n) | (u < 0xf0000000) && @goto ret
    @inbounds b = codeunit(s, i)
    b & 0xc0 == 0x80 || @goto ret
    u |= UInt32(b); i += 1
@label ret
    return reinterpret(Char, u), i
end
# End coppied from InlineStrings.jl

@testset "SubString{String3} (issue #505)" begin
    x = reinterpret(String3, 0x31203203)
    @test x == "1 2"
    y = split(x)[1]
    @test y == "1"
    @test ParseStream(y) isa ParseStream
    @test parsestmt(Expr, y) == parsestmt(Expr, "1")
end
