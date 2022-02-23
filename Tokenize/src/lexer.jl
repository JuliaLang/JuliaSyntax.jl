module Lexers

include("utilities.jl")

import ..Tokens
import ..Tokens: Token, Kind, TokenError, UNICODE_OPS, EMPTY_TOKEN, isliteral

import ..Tokens: FUNCTION, ABSTRACT, IDENTIFIER, BAREMODULE, BEGIN, BREAK, CATCH, CONST, CONTINUE,
                 DO, ELSE, ELSEIF, END, EXPORT, FALSE, FINALLY, FOR, FUNCTION, GLOBAL, LET, LOCAL, IF,
                 IMPORT, MACRO, MODULE, OUTER, QUOTE, RETURN, TRUE, TRY, TYPE, USING, WHILE, ISA, IN,
                 MUTABLE, PRIMITIVE, STRUCT, WHERE


export tokenize

@inline ishex(c::Char) = isdigit(c) || ('a' <= c <= 'f') || ('A' <= c <= 'F')
@inline isbinary(c::Char) = c == '0' || c == '1'
@inline isoctal(c::Char) =  '0' ≤ c ≤ '7'
@inline iswhitespace(c::Char) = Base.isspace(c)

struct StringState
    triplestr::Bool
    raw::Bool
    delim::Char
    paren_depth::Int
end

"""
`Lexer` reads from an input stream and emits a single token each time
`next_token` is called.

Ideally a lexer is stateless but some state is needed here for:
* Disambiguating cases like x' (adjoint) vs 'x' (character literal)
* Tokenizing code within string interpolations
"""
mutable struct Lexer{IO_t <: IO}
    io::IO_t
    io_startpos::Int

    token_start_row::Int
    token_start_col::Int
    token_startpos::Int

    current_row::Int
    current_col::Int
    current_pos::Int

    last_token::Tokens.Kind
    string_states::Vector{StringState}
    charstore::IOBuffer
    chars::Tuple{Char,Char,Char,Char}
    charspos::Tuple{Int,Int,Int,Int}
    doread::Bool
    dotop::Bool
end

function Lexer(io::IO)
    c1 = ' '
    p1 = position(io)
    if eof(io)
        c2, p2 = EOF_CHAR, p1
        c3, p3 = EOF_CHAR, p1
        c4, p4 = EOF_CHAR, p1
    else
        c2 = read(io, Char)
        p2 = position(io)
        if eof(io)
            c3, p3 = EOF_CHAR, p1
            c4, p4 = EOF_CHAR, p1
        else
            c3 = read(io, Char)
            p3 = position(io)
            if eof(io)
                c4, p4 = EOF_CHAR, p1
            else
                c4 = read(io, Char)
                p4 = position(io)
            end
        end
    end
    Lexer(io, position(io), 1, 1, position(io), 1, 1, position(io),
                  Tokens.ERROR, Vector{StringState}(), IOBuffer(),
                  (c1,c2,c3,c4), (p1,p2,p3,p4), false, false)
end
Lexer(str::AbstractString) = Lexer(IOBuffer(str))

"""
    tokenize(x, T = Token)

Returns an `Iterable` containing the tokenized input. Can be reverted by e.g.
`join(untokenize.(tokenize(x)))`. Setting `T` chooses the type of token
produced by the lexer (`Token` or `Token`).
"""
tokenize(x) = Lexer(x)

# Iterator interface
Base.IteratorSize(::Type{<:Lexer}) = Base.SizeUnknown()
Base.IteratorEltype(::Type{<:Lexer}) = Base.HasEltype()
Base.eltype(::Type{<:Lexer}) = Token


function Base.iterate(l::Lexer)
    seekstart(l)
    l.token_startpos = position(l)
    l.token_start_row = 1
    l.token_start_col = 1

    l.current_row = 1
    l.current_col = 1
    l.current_pos = l.io_startpos
    t = next_token(l)
    return t, t.kind == Tokens.ENDMARKER
end

function Base.iterate(l::Lexer, isdone::Any)
    isdone && return nothing
    t = next_token(l)
    return t, t.kind == Tokens.ENDMARKER
end

function Base.show(io::IO, l::Lexer)
    print(io, typeof(l), " at position: ", position(l))
end

"""
    startpos(l::Lexer)

Return the latest `Token`'s starting position.
"""
startpos(l::Lexer) = l.token_startpos

"""
    startpos!(l::Lexer, i::Integer)

Set a new starting position.
"""
startpos!(l::Lexer, i::Integer) = l.token_startpos = i

Base.seekstart(l::Lexer) = seek(l.io, l.io_startpos)

"""
    seek2startpos!(l::Lexer)

Sets the lexer's current position to the beginning of the latest `Token`.
"""
seek2startpos!(l::Lexer) = seek(l, startpos(l))

"""
    peekchar(l::Lexer)

Returns the next character without changing the lexer's state.
"""
peekchar(l::Lexer) = l.chars[2]

"""
dpeekchar(l::Lexer)

Returns the next two characters without changing the lexer's state.
"""
dpeekchar(l::Lexer) = l.chars[2], l.chars[3]

"""
peekchar3(l::Lexer)

Returns the next three characters without changing the lexer's state.
"""
peekchar3(l::Lexer) = l.chars[2], l.chars[3], l.chars[4]

"""
    position(l::Lexer)

Returns the current position.
"""
Base.position(l::Lexer) = l.charspos[1]

"""
    eof(l::Lexer)

Determine whether the end of the lexer's underlying buffer has been reached.
"""# Base.position(l::Lexer) = Base.position(l.io)
eof(l::Lexer) = eof(l.io)

Base.seek(l::Lexer, pos) = seek(l.io, pos)

"""
    start_token!(l::Lexer)

Updates the lexer's state such that the next  `Token` will start at the current
position.
"""
function start_token!(l::Lexer)
    l.token_startpos = l.charspos[1]
    l.token_start_row = l.current_row
    l.token_start_col = l.current_col
end

"""
    readchar(l::Lexer)

Returns the next character and increments the current position.
"""
function readchar end


function readchar(l::Lexer)
    c = readchar(l.io)
    l.chars = (l.chars[2], l.chars[3], l.chars[4], c)
    l.charspos = (l.charspos[2], l.charspos[3], l.charspos[4], position(l.io))
    return l.chars[1]
end

"""
    accept(l::Lexer, f::Union{Function, Char, Vector{Char}, String})

Consumes the next character `c` if either `f::Function(c)` returns true, `c == f`
for `c::Char` or `c in f` otherwise. Returns `true` if a character has been
consumed and `false` otherwise.
"""
@inline function accept(l::Lexer, f::Union{Function, Char, Vector{Char}, String})
    c = peekchar(l)
    if isa(f, Function)
        ok = f(c)
    elseif isa(f, Char)
        ok = c == f
    else
        ok = c in f
    end
    ok && readchar(l)
    return ok
end

"""
    accept_batch(l::Lexer, f)

Consumes all following characters until `accept(l, f)` is `false`.
"""
@inline function accept_batch(l::Lexer, f)
    ok = false
    while accept(l, f)
        ok = true
    end
    return ok
end

"""
    emit(l::Lexer, kind::Kind, err::TokenError=Tokens.NO_ERR)

Returns a `Token` of kind `kind` with contents `str` and starts a new `Token`.
"""
function emit(l::Lexer, kind::Kind, err::TokenError = Tokens.NO_ERR)
    suffix = false
    if optakessuffix(kind)
        while isopsuffix(peekchar(l))
            readchar(l)
            suffix = true
        end
    end

    tok = Token(kind, startpos(l), position(l) - 1, err, l.dotop, suffix)

    l.dotop = false
    l.last_token = kind
    return tok
end

"""
    emit_error(l::Lexer, err::TokenError=Tokens.UNKNOWN)

Returns an `ERROR` token with error `err` and starts a new `Token`.
"""
function emit_error(l::Lexer, err::TokenError = Tokens.UNKNOWN)
    return emit(l, Tokens.ERROR, err)
end


"""
    next_token(l::Lexer)

Returns the next `Token`.
"""
function next_token(l::Lexer, start = true)
    start && start_token!(l)
    if !isempty(l.string_states)
        lex_string_chunk(l)
    else
        _next_token(l, readchar(l))
    end
end

function _next_token(l::Lexer, c)
    if eof(c)
        return emit(l, Tokens.ENDMARKER)
    elseif iswhitespace(c)
        return lex_whitespace(l, c)
    elseif c == '['
        return emit(l, Tokens.LSQUARE)
    elseif c == ']'
        return emit(l, Tokens.RSQUARE)
    elseif c == '{'
        return emit(l, Tokens.LBRACE)
    elseif c == ';'
        return emit(l, Tokens.SEMICOLON)
    elseif c == '}'
        return emit(l, Tokens.RBRACE)
    elseif c == '('
        return emit(l, Tokens.LPAREN)
    elseif c == ')'
        return emit(l, Tokens.RPAREN)
    elseif c == ','
        return emit(l, Tokens.COMMA)
    elseif c == '*'
        return lex_star(l);
    elseif c == '^'
        return lex_circumflex(l);
    elseif c == '@'
        return emit(l, Tokens.AT_SIGN)
    elseif c == '?'
        return emit(l, Tokens.CONDITIONAL)
    elseif c == '$'
        return lex_dollar(l);
    elseif c == '⊻'
        return lex_xor(l);
    elseif c == '~'
        return emit(l, Tokens.APPROX)
    elseif c == '#'
        return lex_comment(l)
    elseif c == '='
        return lex_equal(l)
    elseif c == '!'
        return lex_exclaim(l)
    elseif c == '>'
        return lex_greater(l)
    elseif c == '<'
        return lex_less(l)
    elseif c == ':'
        return lex_colon(l)
    elseif c == '|'
        return lex_bar(l)
    elseif c == '&'
        return lex_amper(l)
    elseif c == '\''
        return lex_prime(l)
    elseif c == '÷'
        return lex_division(l)
    elseif c == '"'
        return lex_quote(l);
    elseif c == '%'
        return lex_percent(l);
    elseif c == '/'
        return lex_forwardslash(l);
    elseif c == '\\'
        return lex_backslash(l);
    elseif c == '.'
        return lex_dot(l);
    elseif c == '+'
        return lex_plus(l);
    elseif c == '-'
        return lex_minus(l);
    elseif c == '−' # \minus '−' treated as hyphen '-'
        return emit(l, accept(l, '=') ? Tokens.MINUS_EQ : Tokens.MINUS)
    elseif c == '`'
        return lex_backtick(l);
    elseif is_identifier_start_char(c)
        return lex_identifier(l, c)
    elseif isdigit(c)
        return lex_digit(l, Tokens.INTEGER)
    elseif (k = get(UNICODE_OPS, c, Tokens.ERROR)) != Tokens.ERROR
        return emit(l, k)
    else
        emit_error(l)
    end
end

# We're inside a string; possibly reading the string characters, or maybe in
# Julia code within an interpolation.
function lex_string_chunk(l)
    state = last(l.string_states)
    if state.paren_depth > 0
        # Read normal Julia code inside an interpolation but track nesting of
        # parentheses.
        c = readchar(l)
        if c == '('
            l.string_states[end] = StringState(state.triplestr, state.raw, state.delim,
                                               state.paren_depth + 1)
            return emit(l, Tokens.LPAREN)
        elseif c == ')'
            l.string_states[end] = StringState(state.triplestr, state.raw, state.delim,
                                               state.paren_depth - 1)
            return emit(l, Tokens.RPAREN)
        else
            return _next_token(l, c)
        end
    end
    pc = peekchar(l)
    if l.last_token == Tokens.EX_OR
        pc = peekchar(l)
        # Interpolated symbol or expression
        if pc == '('
            readchar(l)
            l.string_states[end] = StringState(state.triplestr, state.raw, state.delim,
                                               state.paren_depth + 1)
            return emit(l, Tokens.LPAREN)
        elseif is_identifier_start_char(pc)
            return lex_identifier(l, readchar(l))
        else
            # Getting here is a syntax error - fall through to reading string
            # characters and let the parser deal with it.
        end
    elseif l.last_token == Tokens.IDENTIFIER &&
            !(eof(pc) || is_operator_start_char(pc) || is_never_id_char(pc))
        # Only allow certain characters after interpolated vars
        # https://github.com/JuliaLang/julia/pull/25234
        return emit_error(l, Tokens.INVALID_INTERPOLATION_TERMINATOR)
    end
    if eof(pc)
        return emit(l, Tokens.ENDMARKER)
    elseif !state.raw && pc == '$'
        # Start interpolation
        readchar(l)
        return emit(l, Tokens.EX_OR)
    elseif !state.raw && pc == '\\' && (pc2 = dpeekchar(l)[2];
                                        pc2 == '\r' || pc2 == '\n')
        # Process escaped newline as whitespace
        readchar(l)
        readchar(l)
        if pc2 == '\r' && peekchar(l) == '\n'
            readchar(l)
        end
        while (pc = peekchar(l); pc == ' ' || pc == '\t')
            readchar(l)
        end
        return emit(l, Tokens.WHITESPACE)
    elseif pc == state.delim && string_terminates(l, state.delim, state.triplestr)
        # Terminate string
        pop!(l.string_states)
        readchar(l)
        if state.triplestr
            readchar(l); readchar(l)
            return emit(l, state.delim == '"' ?
                        Tokens.TRIPLE_DQUOTE : Tokens.TRIPLE_BACKTICK)
        else
            return emit(l, state.delim == '"' ? Tokens.DQUOTE : Tokens.BACKTICK)
        end
    end
    # Read a chunk of string characters
    if state.raw
        # Raw strings treat all characters as literals with the exception that
        # the closing quotes can be escaped with an odd number of \ characters.
        while true
            pc = peekchar(l)
            if string_terminates(l, state.delim, state.triplestr) || eof(pc)
                break
            elseif state.triplestr && (pc == '\n' || pc == '\r')
                # triple quoted newline splitting
                readchar(l)
                if pc == '\r' && peekchar(l) == '\n'
                    readchar(l)
                end
                break
            end
            c = readchar(l)
            if c == '\\'
                n = 1
                while peekchar(l) == '\\'
                    readchar(l)
                    n += 1
                end
                if peekchar(l) == state.delim && !iseven(n)
                    readchar(l)
                end
            end
        end
    else
        while true
            pc = peekchar(l)
            if pc == '$' || eof(pc)
                break
            elseif state.triplestr && (pc == '\n' || pc == '\r')
                # triple quoted newline splitting
                readchar(l)
                if pc == '\r' && peekchar(l) == '\n'
                    readchar(l)
                end
                break
            elseif pc == state.delim && string_terminates(l, state.delim, state.triplestr)
                break
            elseif pc == '\\'
                # Escaped newline
                pc2 = dpeekchar(l)[2]
                if pc2 == '\r' || pc2 == '\n'
                    break
                end
            end
            c = readchar(l)
            if c == '\\'
                c = readchar(l)
                eof(c) && break
                continue
            end
        end
    end
    return emit(l, state.delim == '"' ?  Tokens.STRING : Tokens.CMD)
end

# Lex whitespace, a whitespace char `c` has been consumed
function lex_whitespace(l::Lexer, c)
    k = Tokens.WHITESPACE
    while true
        if c == '\n'
            k = Tokens.NEWLINE_WS
        end
        pc = peekchar(l)
        # stop on non whitespace and limit to a single newline in a token
        if !iswhitespace(pc) || (k == Tokens.NEWLINE_WS && pc == '\n')
            break
        end
        c = readchar(l)
    end
    return emit(l, k)
end

function lex_comment(l::Lexer, doemit=true)
    if peekchar(l) != '='
        while true
            pc = peekchar(l)
            if pc == '\n' || eof(pc)
                return doemit ? emit(l, Tokens.COMMENT) : EMPTY_TOKEN(token_type(l))
            end
            readchar(l)
        end
    else
        pc = '#'
        c = readchar(l) # consume the '='
        n_start, n_end = 1, 0
        while true
            if eof(c)
                return doemit ? emit_error(l, Tokens.EOF_MULTICOMMENT) : EMPTY_TOKEN(token_type(l))
            end
            nc = readchar(l)
            if c == '#' && nc == '='
                n_start += 1
            elseif c == '=' && nc == '#' && pc != '#'
                n_end += 1
            end
            if n_start == n_end
                return doemit ? emit(l, Tokens.COMMENT) : EMPTY_TOKEN(token_type(l))
            end
            pc = c
            c = nc
        end
    end
end

# Lex a greater char, a '>' has been consumed
function lex_greater(l::Lexer)
    if accept(l, '>') # >>
        if accept(l, '>') # >>>
            if accept(l, '=') # >>>=
                return emit(l, Tokens.UNSIGNED_BITSHIFT_EQ)
            else # >>>?, ? not a =
                return emit(l, Tokens.UNSIGNED_BITSHIFT)
            end
        elseif accept(l, '=') # >>=
            return emit(l, Tokens.RBITSHIFT_EQ)
        else # '>>'
            return emit(l, Tokens.RBITSHIFT)
        end
    elseif accept(l, '=') # >=
        return emit(l, Tokens.GREATER_EQ)
    elseif accept(l, ':') # >:
        return emit(l, Tokens.ISSUPERTYPE)
    else  # '>'
        return emit(l, Tokens.GREATER)
    end
end

# Lex a less char, a '<' has been consumed
function lex_less(l::Lexer)
    if accept(l, '<') # <<
        if accept(l, '=') # <<=
            return emit(l, Tokens.LBITSHIFT_EQ)
        else # '<<?', ? not =, ' '
            return emit(l, Tokens.LBITSHIFT)
        end
    elseif accept(l, '=') # <=
        return emit(l, Tokens.LESS_EQ)
    elseif accept(l, ':')
        return emit(l, Tokens.ISSUBTYPE)
    elseif accept(l, '|') # <|
        return emit(l, Tokens.LPIPE)
    elseif dpeekchar(l) == ('-', '-') # <-- or <-->
        readchar(l); readchar(l)
        if accept(l, '>')
            return emit(l, Tokens.DOUBLE_ARROW)
        else
            return emit(l, Tokens.LEFT_ARROW)
        end
    else
        return emit(l, Tokens.LESS) # '<'
    end
end

# Lex all tokens that start with an = character.
# An '=' char has been consumed
function lex_equal(l::Lexer)
    if accept(l, '=') # ==
        if accept(l, '=') # ===
            emit(l, Tokens.EQEQEQ)
        else
            emit(l, Tokens.EQEQ)
        end
    elseif accept(l, '>') # =>
        emit(l, Tokens.PAIR_ARROW)
    else
        emit(l, Tokens.EQ)
    end
end

# Lex a colon, a ':' has been consumed
function lex_colon(l::Lexer)
    if accept(l, ':') # '::'
        return emit(l, Tokens.DECLARATION)
    elseif accept(l, '=') # ':='
        return emit(l, Tokens.COLON_EQ)
    else
        return emit(l, Tokens.COLON)
    end
end

function lex_exclaim(l::Lexer)
    if accept(l, '=') # !=
        if accept(l, '=') # !==
            return emit(l, Tokens.NOT_IS)
        else # !=
            return emit(l, Tokens.NOT_EQ)
        end
    else
        return emit(l, Tokens.NOT)
    end
end

function lex_percent(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.REM_EQ)
    else
        return emit(l, Tokens.REM)
    end
end

function lex_bar(l::Lexer)
    if accept(l, '=') # |=
        return emit(l, Tokens.OR_EQ)
    elseif accept(l, '>') # |>
        return emit(l, Tokens.RPIPE)
    elseif accept(l, '|') # ||
        return emit(l, Tokens.LAZY_OR)
    else
        emit(l, Tokens.OR) # '|'
    end
end

function lex_plus(l::Lexer)
    if accept(l, '+')
        return emit(l, Tokens.PLUSPLUS)
    elseif accept(l, '=')
        return emit(l, Tokens.PLUS_EQ)
    end
    return emit(l, Tokens.PLUS)
end

function lex_minus(l::Lexer)
    if accept(l, '-')
        if accept(l, '>')
            return emit(l, Tokens.RIGHT_ARROW)
        else
            return emit_error(l, Tokens.INVALID_OPERATOR) # "--" is an invalid operator
        end
    elseif accept(l, '>')
        return emit(l, Tokens.ANON_FUNC)
    elseif accept(l, '=')
        return emit(l, Tokens.MINUS_EQ)
    end
    return emit(l, Tokens.MINUS)
end

function lex_star(l::Lexer)
    if accept(l, '*')
        return emit_error(l, Tokens.INVALID_OPERATOR) # "**" is an invalid operator use ^
    elseif accept(l, '=')
        return emit(l, Tokens.STAR_EQ)
    end
    return emit(l, Tokens.STAR)
end

function lex_circumflex(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.CIRCUMFLEX_EQ)
    end
    return emit(l, Tokens.CIRCUMFLEX_ACCENT)
end

function lex_division(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.DIVISION_EQ)
    end
    return emit(l, Tokens.DIVISION_SIGN)
end

function lex_dollar(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.EX_OR_EQ)
    end
    return emit(l, Tokens.EX_OR)
end

function lex_xor(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.XOR_EQ)
    end
    return emit(l, Tokens.XOR)
end

function accept_number(l::Lexer, f::F) where {F}
    while true
        pc, ppc = dpeekchar(l)
        if pc == '_' && !f(ppc)
            return
        elseif f(pc) || pc == '_'
            readchar(l)
        else
            return
        end
    end
end

# A digit has been consumed
function lex_digit(l::Lexer, kind)
    accept_number(l, isdigit)
    pc,ppc = dpeekchar(l)
    if pc == '.'
        if kind === Tokens.FLOAT
            # If we enter the function with kind == FLOAT then a '.' has been parsed.
            readchar(l)
            return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
        elseif ppc == '.'
            return emit(l, kind)
        elseif is_operator_start_char(ppc) && ppc !== ':'
            readchar(l)
            return emit_error(l)
        elseif (!(isdigit(ppc) ||
            iswhitespace(ppc) ||
            is_identifier_start_char(ppc)
            || ppc == '('
            || ppc == ')'
            || ppc == '['
            || ppc == ']'
            || ppc == '{'
            || ppc == '}'
            || ppc == ','
            || ppc == ';'
            || ppc == '@'
            || ppc == '`'
            || ppc == '"'
            || ppc == ':'
            || ppc == '?'
            || eof(ppc)))
            kind = Tokens.INTEGER

            return emit(l, kind)
        end
        readchar(l)

        kind = Tokens.FLOAT
        accept_number(l, isdigit)
        pc, ppc = dpeekchar(l)
        if (pc == 'e' || pc == 'E' || pc == 'f') && (isdigit(ppc) || ppc == '+' || ppc == '-' || ppc == '−')
            kind = Tokens.FLOAT
            readchar(l)
            accept(l, "+-−")
            if accept_batch(l, isdigit)
                pc,ppc = dpeekchar(l)
                if pc === '.' && !dotop2(ppc, ' ')
                    accept(l, '.')
                    return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
                end
            else
                return emit_error(l)
            end
        elseif pc == '.' && (is_identifier_start_char(ppc) || eof(ppc))
            readchar(l)
            return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
        end

    elseif (pc == 'e' || pc == 'E' || pc == 'f') && (isdigit(ppc) || ppc == '+' || ppc == '-' || ppc == '−')
        kind = Tokens.FLOAT
        readchar(l)
        accept(l, "+-−")
        if accept_batch(l, isdigit)
            pc,ppc = dpeekchar(l)
            if pc === '.' && !dotop2(ppc, ' ')
                accept(l, '.')
                return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
            end
        else
            return emit_error(l)
        end
    elseif position(l) - startpos(l) == 1 && l.chars[1] == '0'
        kind == Tokens.INTEGER
        if pc == 'x'
            kind = Tokens.HEX_INT
            isfloat = false
            readchar(l)
            !(ishex(ppc) || ppc == '.') && return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
            accept_number(l, ishex)
            if accept(l, '.')
                accept_number(l, ishex)
                isfloat = true
            end
            if accept(l, "pP")
                kind = Tokens.FLOAT
                accept(l, "+-−")
                accept_number(l, isdigit)
            elseif isfloat
                return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
            end
        elseif pc == 'b'
            !isbinary(ppc) && return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
            readchar(l)
            accept_number(l, isbinary)
            kind = Tokens.BIN_INT
        elseif pc == 'o'
            !isoctal(ppc) && return emit_error(l, Tokens.INVALID_NUMERIC_CONSTANT)
            readchar(l)
            accept_number(l, isoctal)
            kind = Tokens.OCT_INT
        end
    end
    return emit(l, kind)
end

function lex_prime(l, doemit = true)
    if l.last_token == Tokens.IDENTIFIER ||
        Tokens.iscontextualkeyword(l.last_token) ||
        Tokens.iswordoperator(l.last_token) ||
        l.last_token == Tokens.DOT ||
        l.last_token ==  Tokens.RPAREN ||
        l.last_token ==  Tokens.RSQUARE ||
        l.last_token ==  Tokens.RBRACE ||
        l.last_token == Tokens.PRIME ||
        l.last_token == Tokens.END || isliteral(l.last_token)
        return emit(l, Tokens.PRIME)
    else
        if accept(l, '\'')
            if accept(l, '\'')
                return doemit ? emit(l, Tokens.CHAR) : EMPTY_TOKEN(token_type(l))
            else
                # Empty char literal
                # Arguably this should be an error here, but we generally
                # look at the contents of the char literal in the parser,
                # so we defer erroring until there.
                return doemit ? emit(l, Tokens.CHAR) : EMPTY_TOKEN(token_type(l))
            end
        end
        while true
            c = readchar(l)
            if eof(c)
                return doemit ? emit_error(l, Tokens.EOF_CHAR) : EMPTY_TOKEN(token_type(l))
            elseif c == '\\'
                if eof(readchar(l))
                    return doemit ? emit_error(l, Tokens.EOF_CHAR) : EMPTY_TOKEN(token_type(l))
                end
            elseif c == '\''
                return doemit ? emit(l, Tokens.CHAR) : EMPTY_TOKEN(token_type(l))
            end
        end
    end
end

function lex_amper(l::Lexer)
    if accept(l, '&')
        return emit(l, Tokens.LAZY_AND)
    elseif accept(l, '=')
        return emit(l, Tokens.AND_EQ)
    else
        return emit(l, Tokens.AND)
    end
end

# Parse a token starting with a quote.
# A '"' has been consumed
function lex_quote(l::Lexer)
    raw = l.last_token == Tokens.IDENTIFIER ||
          Tokens.iscontextualkeyword(l.last_token) ||
          Tokens.iswordoperator(l.last_token)
    pc, dpc = dpeekchar(l)
    triplestr = pc == '"' && dpc == '"'
    push!(l.string_states, StringState(triplestr, raw, '"', 0))
    if triplestr
        readchar(l)
        readchar(l)
        emit(l, Tokens.TRIPLE_DQUOTE)
    else
        emit(l, Tokens.DQUOTE)
    end
end

function string_terminates(l, delim::Char, triplestr::Bool)
    if triplestr
        c1, c2, c3 = peekchar3(l)
        c1 === delim && c2 === delim && c3 === delim
    else
        peekchar(l) === delim
    end
end

# Parse a token starting with a forward slash.
# A '/' has been consumed
function lex_forwardslash(l::Lexer)
    if accept(l, '/') # //
        if accept(l, '=') # //=
            return emit(l, Tokens.FWDFWD_SLASH_EQ)
        else
            return emit(l, Tokens.FWDFWD_SLASH)
        end
    elseif accept(l, '=') # /=
        return emit(l, Tokens.FWD_SLASH_EQ)
    else
        return emit(l, Tokens.FWD_SLASH)
    end
end

function lex_backslash(l::Lexer)
    if accept(l, '=')
        return emit(l, Tokens.BACKSLASH_EQ)
    end
    return emit(l, Tokens.BACKSLASH)
end

# TODO .op
function lex_dot(l::Lexer)
    if accept(l, '.')
        if accept(l, '.')
            return emit(l, Tokens.DDDOT)
        else
            return emit(l, Tokens.DDOT)
        end
    elseif Base.isdigit(peekchar(l))
        return lex_digit(l, Tokens.FLOAT)
    else
        pc, dpc = dpeekchar(l)
        if dotop1(pc)
            l.dotop = true
            return _next_token(l, readchar(l))
        elseif pc =='+'
            l.dotop = true
            readchar(l)
            return lex_plus(l)
        elseif pc =='-'
            l.dotop = true
            readchar(l)
            return lex_minus(l)
        elseif pc == '−'
            l.dotop = true
            readchar(l)
            return emit(l, accept(l, '=') ? Tokens.MINUS_EQ : Tokens.MINUS)
        elseif pc =='*'
            l.dotop = true
            readchar(l)
            return lex_star(l)
        elseif pc =='/'
            l.dotop = true
            readchar(l)
            return lex_forwardslash(l)
        elseif pc =='\\'
            l.dotop = true
            readchar(l)
            return lex_backslash(l)
        elseif pc =='^'
            l.dotop = true
            readchar(l)
            return lex_circumflex(l)
        elseif pc =='<'
            l.dotop = true
            readchar(l)
            return lex_less(l)
        elseif pc =='>'
            l.dotop = true
            readchar(l)
            return lex_greater(l)
        elseif pc =='&'
            l.dotop = true
            readchar(l)
            if accept(l, '=')
                return emit(l, Tokens.AND_EQ)
            else
                if accept(l, '&')
                    return emit(l, Tokens.LAZY_AND)
                end
                return emit(l, Tokens.AND)
            end
        elseif pc =='%'
            l.dotop = true
            readchar(l)
            return lex_percent(l)
        elseif pc == '=' && dpc != '>'
            l.dotop = true
            readchar(l)
            return lex_equal(l)
        elseif pc == '|'
            l.dotop = true
            readchar(l)
            if accept(l, '|')
                return emit(l, Tokens.LAZY_OR)
            end
            return lex_bar(l)
        elseif pc == '!' && dpc == '='
            l.dotop = true
            readchar(l)
            return lex_exclaim(l)
        elseif pc == '⊻'
            l.dotop = true
            readchar(l)
            return lex_xor(l)
        elseif pc == '÷'
            l.dotop = true
            readchar(l)
            return lex_division(l)
        elseif pc == '=' && dpc == '>'
            l.dotop = true
            readchar(l)
            return lex_equal(l)
        end
        return emit(l, Tokens.DOT)
    end
end

# A ` has been consumed
function lex_backtick(l::Lexer)
    pc, dpc = dpeekchar(l)
    triplestr = pc == '`' && dpc == '`'
    # Backticks always contain raw strings only. See discussion on bug
    # https://github.com/JuliaLang/julia/issues/3150
    raw = true
    push!(l.string_states, StringState(triplestr, raw, '`', 0))
    if triplestr
        readchar(l)
        readchar(l)
        emit(l, Tokens.TRIPLE_BACKTICK)
    else
        emit(l, Tokens.BACKTICK)
    end
end

const MAX_KW_LENGTH = 10
function lex_identifier(l::Lexer, c)
    h = simple_hash(c, UInt64(0))
    n = 1
    while true
        pc, ppc = dpeekchar(l)
        if (pc == '!' && ppc == '=') || !is_identifier_char(pc)
            break
        end
        c = readchar(l)
        h = simple_hash(c, h)
        n += 1
    end

    if n > MAX_KW_LENGTH
        emit(l, IDENTIFIER)
    else
        emit(l, get(kw_hash, h, IDENTIFIER))
    end
end

# This creates a hash for chars in [a-z] using 5 bit per char.
# Requires an additional input-length check somewhere, because
# this only works up to ~12 chars.
@inline function simple_hash(c::Char, h::UInt64)
    bytehash = (clamp(c - 'a' + 1, -1, 30) % UInt8) & 0x1f
    h << 5 + bytehash
end

function simple_hash(str)
    ind = 1
    h = UInt64(0)
    while ind <= length(str)
        h = simple_hash(str[ind], h)
        ind = nextind(str, ind)
    end
    h
end

kws = [
Tokens.BAREMODULE,
Tokens.BEGIN,
Tokens.BREAK,
Tokens.CATCH,
Tokens.CONST,
Tokens.CONTINUE,
Tokens.DO,
Tokens.ELSE,
Tokens.ELSEIF,
Tokens.END,
Tokens.EXPORT,
Tokens.FINALLY,
Tokens.FOR,
Tokens.FUNCTION,
Tokens.GLOBAL,
Tokens.IF,
Tokens.IMPORT,
Tokens.LET,
Tokens.LOCAL,
Tokens.MACRO,
Tokens.MODULE,
Tokens.QUOTE,
Tokens.RETURN,
Tokens.STRUCT,
Tokens.TRY,
Tokens.USING,
Tokens.WHILE,
Tokens.IN,
Tokens.ISA,
Tokens.WHERE,
Tokens.TRUE,
Tokens.FALSE,

Tokens.ABSTRACT,
Tokens.AS,
Tokens.DOC,
Tokens.MUTABLE,
Tokens.OUTER,
Tokens.PRIMITIVE,
Tokens.TYPE,
Tokens.VAR,
]

const kw_hash = Dict(simple_hash(lowercase(string(kw))) => kw for kw in kws)

end # module
