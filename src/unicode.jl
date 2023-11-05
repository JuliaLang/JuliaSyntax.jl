# this is a mirror of some of Base.Unicode and related functions,
# but using the utf8proc_jll version tied to JuliaSyntax, so that
# the supported Unicode version is the same across Julia versions.

module Unicode

export category_code, normalize_identifier, is_identifier_char, is_identifier_start_char

using utf8proc_jll: libutf8proc

# these constants have been stable across all utf8proc versions,
# so no need to redefine them:
import Base.Unicode: UTF8PROC_CATEGORY_CN, UTF8PROC_CATEGORY_LU, UTF8PROC_CATEGORY_LL, UTF8PROC_CATEGORY_LT, UTF8PROC_CATEGORY_LM, UTF8PROC_CATEGORY_LO, UTF8PROC_CATEGORY_MN, UTF8PROC_CATEGORY_MC, UTF8PROC_CATEGORY_ME, UTF8PROC_CATEGORY_ND, UTF8PROC_CATEGORY_NL, UTF8PROC_CATEGORY_NO, UTF8PROC_CATEGORY_PC, UTF8PROC_CATEGORY_PD, UTF8PROC_CATEGORY_PS, UTF8PROC_CATEGORY_PE, UTF8PROC_CATEGORY_PI, UTF8PROC_CATEGORY_PF, UTF8PROC_CATEGORY_PO, UTF8PROC_CATEGORY_SM, UTF8PROC_CATEGORY_SC, UTF8PROC_CATEGORY_SK, UTF8PROC_CATEGORY_SO, UTF8PROC_CATEGORY_ZS, UTF8PROC_CATEGORY_ZL, UTF8PROC_CATEGORY_ZP, UTF8PROC_CATEGORY_CC, UTF8PROC_CATEGORY_CF, UTF8PROC_CATEGORY_CS, UTF8PROC_CATEGORY_CO

using Base: ismalformed

#####################################################################
# functions copied almost as-is from Base.Unicode, with the only change
# being that they now ccall into utf8proc_jll.

utf8proc_error(result) = error(unsafe_string(ccall((:utf8proc_errmsg,libutf8proc), Cstring, (Cssize_t,), result)))

# Stateful grapheme break required by Unicode-9 rules: the string
# must be processed in sequence, with state initialized to Ref{Int32}(0).
# Requires utf8proc v2.0 or later.
function isgraphemebreak!(state::Ref{Int32}, c1::AbstractChar, c2::AbstractChar)
    if ismalformed(c1) || ismalformed(c2)
        state[] = 0
        return true
    end
    ccall((:utf8proc_grapheme_break_stateful,libutf8proc), Bool,
          (UInt32, UInt32, Ref{Int32}), c1, c2, state)
end

# returns UTF8PROC_CATEGORY code in 0:30 giving Unicode category
function category_code(c::AbstractChar)
    !ismalformed(c) ? category_code(UInt32(c)) : Cint(31)
end

function category_code(x::Integer)
    x ≤ 0x10ffff ? ccall((:utf8proc_category,libutf8proc), Cint, (UInt32,), x) : Cint(30)
end

@inline isspace(c::AbstractChar) =
    c == ' ' || '\t' <= c <= '\r' || c == '\u85' ||
    '\ua0' <= c && category_code(c) == UTF8PROC_CATEGORY_ZS

#####################################################################
# Julia identifier normalization, closely based on functions
# from Base.Unicode except that we hard-code the Julia
# chartransform (working around JuliaLang/julia#45716)

# Julia's custom character normalization mapping, based on
# julia/src/flisp/julia_charmap.h:
function julia_custom_func(codepoint::UInt32, ::Ptr{Cvoid})::UInt32
    (codepoint < 0x007f ? codepoint : # optimize for ASCII common case
    codepoint == 0x025B ? 0x03B5 :  # 'ɛ' => 'ε'
    codepoint == 0x00B5 ? 0x03BC :   # 'µ' => 'μ'
    codepoint == 0x00B7 ? 0x22C5 :   # '·' => '⋅'
    codepoint == 0x0387 ? 0x22C5 :   # '·' => '⋅'
    codepoint == 0x2212 ? 0x002D :   # '−' (\minus) => '-'
    codepoint == 0x210F ? 0x0127 :   # 'ℏ' (\hslash) => 'ħ' \hbar
    codepoint)
end

function utf8proc_decompose_julia(str, options, buffer, nwords)
    ret = ccall((:utf8proc_decompose_custom,libutf8proc), Int, (Ptr{UInt8}, Int, Ptr{UInt8}, Int, Cint, Ptr{Cvoid}, Ptr{Cvoid}),
                str, sizeof(str), buffer, nwords, options,
                @cfunction(julia_custom_func, UInt32, (UInt32, Ptr{Cvoid})), C_NULL)
    ret < 0 && utf8proc_error(ret)
    return ret
end

function utf8proc_map_julia(str::Union{String,SubString{String}}, options::Integer, chartransform=identity)
    nwords = utf8proc_decompose_julia(str, options, C_NULL, 0)
    buffer = Base.StringVector(nwords*4)
    nwords = utf8proc_decompose_julia(str, options, buffer, nwords)
    nbytes = ccall((:utf8proc_reencode,libutf8proc), Int, (Ptr{UInt8}, Int, Cint), buffer, nwords, options)
    nbytes < 0 && utf8proc_error(nbytes)
    return String(resize!(buffer, nbytes))
end

function normalize_identifier(str)
    # note that the values of UTF8PROC_x constants have not changed
    # over many utf8proc versions, so we can use them from Base.Unicode
    flags = Base.Unicode.UTF8PROC_STABLE | Base.Unicode.UTF8PROC_COMPOSE
    return isascii(str) ? str : utf8proc_map_julia(str, flags)
end

#####################################################################
# Julia identifier parsing predicates

function is_identifier_char(c::Char)
    # c == EOF_CHAR && return false # covered by isvalid check
    isvalid(c) || return false
    return Base.is_id_char(c)
end

function is_identifier_start_char(c::Char)
    # c == EOF_CHAR && return false # covered by isvalid check
    isvalid(c) || return false
    return Base.is_id_start_char(c)
end

#####################################################################

end
