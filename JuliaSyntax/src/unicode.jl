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

# doesn't check validity of x:
@inline _category_code(x::Integer) = ccall((:utf8proc_category,libutf8proc), Cint, (UInt32,), x)

function category_code(x::Integer)
    x ≤ 0x10ffff ? _category_code(x) : Cint(30)
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

# port of is_wc_cat_id_start from julia/src/flisp/julia_extensions.c
function _is_identifier_start_char(c::UInt32, cat::Integer)
    return (cat == UTF8PROC_CATEGORY_LU || cat == UTF8PROC_CATEGORY_LL ||
            cat == UTF8PROC_CATEGORY_LT || cat == UTF8PROC_CATEGORY_LM ||
            cat == UTF8PROC_CATEGORY_LO || cat == UTF8PROC_CATEGORY_NL ||
            cat == UTF8PROC_CATEGORY_SC ||  # allow currency symbols
            # other symbols, but not arrows or replacement characters
            (cat == UTF8PROC_CATEGORY_SO && !(c >= 0x2190 && c <= 0x21FF) &&
             c != 0xfffc && c != 0xfffd &&
             c != 0x233f &&  # notslash
             c != 0x00a6) || # broken bar

            # math symbol (category Sm) whitelist
            (c >= 0x2140 && c <= 0x2a1c &&
             ((c >= 0x2140 && c <= 0x2144) || # ⅀, ⅁, ⅂, ⅃, ⅄
              c == 0x223f || c == 0x22be || c == 0x22bf || # ∿, ⊾, ⊿
              c == 0x22a4 || c == 0x22a5 ||   # ⊤ ⊥

              (c >= 0x2200 && c <= 0x2233 &&
               (c == 0x2202 || c == 0x2205 || c == 0x2206 || # ∂, ∅, ∆
                c == 0x2207 || c == 0x220e || c == 0x220f || # ∇, ∎, ∏
                c == 0x2200 || c == 0x2203 || c == 0x2204 || # ∀, ∃, ∄
                c == 0x2210 || c == 0x2211 || # ∐, ∑
                c == 0x221e || c == 0x221f || # ∞, ∟
                c >= 0x222b)) || # ∫, ∬, ∭, ∮, ∯, ∰, ∱, ∲, ∳

              (c >= 0x22c0 && c <= 0x22c3) ||  # N-ary big ops: ⋀, ⋁, ⋂, ⋃
              (c >= 0x25F8 && c <= 0x25ff) ||  # ◸, ◹, ◺, ◻, ◼, ◽, ◾, ◿

              (c >= 0x266f &&
               (c == 0x266f || c == 0x27d8 || c == 0x27d9 || # ♯, ⟘, ⟙
                (c >= 0x27c0 && c <= 0x27c1) ||  # ⟀, ⟁
                (c >= 0x29b0 && c <= 0x29b4) ||  # ⦰, ⦱, ⦲, ⦳, ⦴
                (c >= 0x2a00 && c <= 0x2a06) ||  # ⨀, ⨁, ⨂, ⨃, ⨄, ⨅, ⨆
                (c >= 0x2a09 && c <= 0x2a16) ||  # ⨉, ⨊, ⨋, ⨌, ⨍, ⨎, ⨏, ⨐, ⨑, ⨒, ⨓, ⨔, ⨕, ⨖
                c == 0x2a1b || c == 0x2a1c)))) || # ⨛, ⨜

            (c >= 0x1d6c1 && # variants of \nabla and \partial
             (c == 0x1d6c1 || c == 0x1d6db ||
              c == 0x1d6fb || c == 0x1d715 ||
              c == 0x1d735 || c == 0x1d74f ||
              c == 0x1d76f || c == 0x1d789 ||
              c == 0x1d7a9 || c == 0x1d7c3)) ||

            # super- and subscript +-=()
            (c >= 0x207a && c <= 0x207e) ||
            (c >= 0x208a && c <= 0x208e) ||

            # angle symbols
            (c >= 0x2220 && c <= 0x2222) || # ∠, ∡, ∢
            (c >= 0x299b && c <= 0x29af) || # ⦛, ⦜, ⦝, ⦞, ⦟, ⦠, ⦡, ⦢, ⦣, ⦤, ⦥, ⦦, ⦧, ⦨, ⦩, ⦪, ⦫, ⦬, ⦭, ⦮, ⦯

            # Other_ID_Start
            c == 0x2118 || c == 0x212E || # ℘, ℮
            (c >= 0x309B && c <= 0x309C) || # katakana-hiragana sound marks

            # bold-digits and double-struck digits
            (c >= 0x1D7CE && c <= 0x1D7E1)) # 𝟎 through 𝟗 (inclusive), 𝟘 through 𝟡 (inclusive)
end

# from jl_id_start_char in julia/src/flisp/julia_extensions.c
function is_identifier_start_char(c::Char)
    if (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'
        return true
    end
    if c < Char(0xA1) || !isvalid(c)
        return false
    end
    x = UInt32(c)
    return _is_identifier_start_char(x, _category_code(x))
end

# from jl_id_char in julia/src/flisp/julia_extensions.c
function is_identifier_char(c::Char)
    if (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_' ||
       (c >= '0' && c <= '9') || c == '!'
        return true
    end
    if c < Char(0xA1) || !isvalid(c)
        return false
    end
    x = UInt32(c)
    cat = _category_code(x)
    _is_identifier_start_char(x, cat) && return true
    if (cat == UTF8PROC_CATEGORY_MN || cat == UTF8PROC_CATEGORY_MC ||
        cat == UTF8PROC_CATEGORY_ND || cat == UTF8PROC_CATEGORY_PC ||
        cat == UTF8PROC_CATEGORY_SK || cat == UTF8PROC_CATEGORY_ME ||
        cat == UTF8PROC_CATEGORY_NO ||
        # primes (single, double, triple, their reverses, and quadruple)
        (x >= 0x2032 && x <= 0x2037) || (x == 0x2057))
        return true
    end
    return false
end

#####################################################################

end
