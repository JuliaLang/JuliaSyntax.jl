# A prototype for converting JuliaSyntax data structures into CSTParser.EXPR.

using CSTParser

using JuliaSyntax
using JuliaSyntax: GreenNode, SyntaxHead, SourceFile, TaggedRange,
    @K_str, @KSet_cmd,
    haschildren, is_syntax_kind, is_keyword, is_operator, is_identifier, head, kind, span,
    is_infix, is_trivia, untokenize, TzTokens, children

# See CSTParser.tokenkindtoheadmap
function tokenkindtoheadmap(k::TzTokens.Kind)
    k === TzTokens.COMMA      ? :COMMA   :
    k === TzTokens.LPAREN     ? :LPAREN  :
    k === TzTokens.RPAREN     ? :RPAREN  :
    k === TzTokens.LSQUARE    ? :LSQUARE :
    k === TzTokens.RSQUARE    ? :RSQUARE :
    k === TzTokens.LBRACE     ? :LBRACE  :
    k === TzTokens.RBRACE     ? :RBRACE  :
    k === TzTokens.AT_SIGN    ? :ATSIGN  :
    k === TzTokens.DOT        ? :DOT     :
    k === TzTokens.ABSTRACT   ? :ABSTRACT :
    k === TzTokens.BAREMODULE ? :BAREMODULE :
    k === TzTokens.BEGIN      ? :BEGIN :
    k === TzTokens.BREAK      ? :BREAK :
    k === TzTokens.CATCH      ? :CATCH :
    k === TzTokens.CONST      ? :CONST :
    k === TzTokens.CONTINUE   ? :CONTINUE :
    k === TzTokens.DO         ? :DO :
    k === TzTokens.ELSE       ? :ELSE :
    k === TzTokens.ELSEIF     ? :ELSEIF :
    k === TzTokens.END        ? :END :
    k === TzTokens.EXPORT     ? :EXPORT :
    k === TzTokens.FINALLY    ? :FINALLY :
    k === TzTokens.FOR        ? :FOR :
    k === TzTokens.FUNCTION   ? :FUNCTION :
    k === TzTokens.GLOBAL     ? :GLOBAL :
    k === TzTokens.IF         ? :IF :
    k === TzTokens.IMPORT     ? :IMPORT :
    k === TzTokens.LET        ? :LET :
    k === TzTokens.LOCAL      ? :LOCAL :
    k === TzTokens.MACRO      ? :MACRO :
    k === TzTokens.MODULE     ? :MODULE :
    k === TzTokens.MUTABLE    ? :MUTABLE :
    k === TzTokens.OUTER      ? :OUTER :
    k === TzTokens.PRIMITIVE  ? :PRIMITIVE :
    k === TzTokens.QUOTE      ? :QUOTE :
    k === TzTokens.RETURN     ? :RETURN :
    k === TzTokens.STRUCT     ? :STRUCT :
    k === TzTokens.TRY        ? :TRY :
    k === TzTokens.TYPE       ? :TYPE :
    k === TzTokens.USING      ? :USING :
    k === TzTokens.WHILE      ? :WHILE :
    k === TzTokens.INTEGER    ? :INTEGER :
    k === TzTokens.BIN_INT    ? :BININT :
    k === TzTokens.HEX_INT    ? :HEXINT :
    k === TzTokens.OCT_INT    ? :OCTINT :
    k === TzTokens.FLOAT      ? :FLOAT :
    k === TzTokens.STRING     ? :STRING :
    # k === TzTokens.TRIPLE_STRING ? :TRIPLESTRING :
    k === TzTokens.CHAR       ? :CHAR :
    k === TzTokens.CMD        ? :CMD :
    # k === TzTokens.TRIPLE_CMD ? :TRIPLECMD :
    k === TzTokens.TRUE       ? :TRUE :
    k === TzTokens.FALSE      ? :FALSE :
    k === TzTokens.ENDMARKER  ? :errortoken :
        error("Unknown token $k")
end

# Things which are "trailing trivia" according to CSTParser
#
# "Trailing trivia" is trivia which will be attached to the end of a node.
is_cst_trailing_trivia(x) = kind(x) in KSet`Whitespace NewlineWs Comment ;`

# Convert GreenNode into CSTParser.EXPR
function cst(source::SourceFile, raw_node::GreenNode{SyntaxHead}, position::Integer=1)
    node_start = position
    cs = children(raw_node)
    i = 1
    args   = CSTParser.EXPR[]
    trivia = CSTParser.EXPR[]
    last_trivia_span = 0
    while i <= length(cs)
        raw = cs[i]
        if haschildren(raw)
            c = cst(source, raw, position)
            push!(args, c)
            last_trivia_span = c.fullspan - c.span
            position += span(raw)
        else
            start_pos = position
            token_start = i
            inner_span = span(raw)
            position += span(raw)
            # Here we append any trailing trivia tokens to the node.
            while i < length(cs) && is_cst_trailing_trivia(cs[i+1])
                position += span(cs[i+1])
                i += 1
            end
            full_span = position - start_pos
            last_trivia_span = full_span - inner_span

            # Leaf node
            k = kind(raw)
            val_range = start_pos:(start_pos + inner_span - 1)
            val = source[val_range]

            if kind(raw) == K"nothing"
                # First `nothing` token in file seems to require this. Why I don't know.
                inner_span = full_span
            end

            # See CSTParser.literalmap. Which we can't use directly because we've
            # customized Tokenize.jl :-(
            cst_head = k === TzTokens.NOTHING    ? :NOTHING :
                       # FIXME: Following probably need special handling
                       k === TzTokens.MACRO_NAME ? :IDENTIFIER :
                       k === TzTokens.CMD_MACRO_NAME ? :IDENTIFIER :
                       k === TzTokens.STRING_MACRO_NAME ? :IDENTIFIER :
                       k === TzTokens.DQUOTE     ? :DQUOTE :
                       k === TzTokens.BACKTICK   ? :BACKTICK :
                       is_operator(k)            ? :OPERATOR :
                       is_identifier(k)          ? :IDENTIFIER :
                       tokenkindtoheadmap(k)
            # FIXME: STRING, TRIPLE_STRING, CMD, TRIPLE_CMD, need special handling:
            #  * STRING        doesn't incude delimiters (DQUOTE tokens)
            #  * CMD           doesn't include delimiters (BACKTICK tokens)
            #  * TRIPLE_STRING is a composite of STRING and TRIPLE_DQUOTE
            #  * TRIPLE_CMD    is a composite of CMD and TRIPLE_BACKTICK
            # They don't exist anymore as individual tokens

            push!(is_trivia(raw) ? trivia : args,
                  CSTParser.EXPR(cst_head, nothing, nothing, full_span, inner_span, val,
                                 nothing, nothing))
        end
        i += 1
    end

    if is_infix(raw_node)
        args[1], args[2] = args[2], args[1]
        # TODO: Other argument swizzling, as done in SyntaxNode -> Expr conversions
    end

    full_span = position - node_start
    inner_span = full_span - last_trivia_span
    k = kind(raw_node)
    cst_head = k == K"toplevel" ? :file :
               is_operator(k)   ? popfirst!(trivia) :
               Symbol(lowercase(string(kind(raw_node))))
    x = CSTParser.EXPR(cst_head, args,
                       isempty(trivia) ? nothing : trivia,
                       full_span, inner_span, nothing, nothing, nothing)
    for a in args
        a.parent = x
    end
    for a in trivia
        a.parent = x
    end
    return x
end


# Some steps of conversion to CSTParser.EXPR is most conveniently done on the
# raw ParseStream representation. In particular, CSTParser.EXPR attaches
# some types of trivia to the end of nontrivia or trivia tokens.
#
# This function reassociates trivia with nonterminal nodes to make converting
# to CSTParser.EXPR a *local* operation on green tree nodes.
function parse_for_cst(text)
    stream = JuliaSyntax.ParseStream(text)

    # Insert initial nothing node if necessary to anchor trailing whitespace.
    if is_cst_trailing_trivia(peek(stream, skip_whitespace=false))
        JuliaSyntax.bump_invisible(stream, K"nothing")
    end
    JuliaSyntax.parse(stream, rule=:toplevel)

    # Fix up start of stream
    ranges = stream.ranges
    @assert kind(ranges[end]) == K"toplevel"
    ranges[end] = let r = ranges[end]
        TaggedRange(r.head, 1, r.last_token)
    end

    # Rearrange whitespace trivia tokens so that they're always *trailing*
    # siblings of non-whitespace trivia tokens.
    #
    # This is required for later conversion to CSTParser.EXPR
    tokens = stream.tokens
    for (i,range) in enumerate(ranges)
        first_token = range.first_token
        while first_token < length(tokens) &&
                is_cst_trailing_trivia(tokens[first_token])
            first_token += 1
        end
        last_token = range.last_token
        while last_token < length(tokens) && 
                is_cst_trailing_trivia(tokens[last_token+1])
            last_token += 1
        end
        ranges[i] = TaggedRange(head(range), first_token, last_token)
    end

    return JuliaSyntax.build_tree(JuliaSyntax.GreenNode, stream)
end

# CSTParser.EXPR equality; should be in CSTParser...
function Base.:(==)(x::CSTParser.EXPR, y::CSTParser.EXPR)
    # Debugging hacks:
    if x.head != y.head
        @info "Trivia mismatch" x.head y.head
    end
    if x.trivia != y.trivia
        @info "Trivia mismatch" x.trivia y.trivia
    end
    if x.fullspan != y.fullspan
        @info "Fullspan mismatch" x y x.fullspan y.fullspan
    end
    if x.span != y.span
        @info "Span mismatch" x y x.span y.span
    end
    if x.val != y.val
        @info "Trivia mismatch" x.val y.val
    end

    return x.head == y.head &&
           x.args == y.args &&
           x.trivia == y.trivia &&
           x.fullspan == y.fullspan &&
           x.span == y.span &&
           x.val == y.val &&
           x.meta == y.meta
end

# Some things which work
#text = " 1 + 2 * 3 "
#text = "[ 1 ; 2 ;]"
#text = "for i=1:10\nx\ny\nend"
#text = "100.00"
text = """
function f(x,y)
    s = 0
    for i = 1:10
        s += x - i^y
    end
end
"""

# Some things which don't yet work
#
# Macro names
# text = "@A.asdf x y"
#
# Bracket nodes don't exist yet in JuliaSyntax
# text = "(a + b)"
#
# Strings have separate delimiters. Will need to put them back together.
# text = "\"str\""

source = SourceFile(text)

ex = parse_for_cst(text)
# show(stdout, MIME"text/plain"(), ex, text)

y = CSTParser.parse(text, true)
x = cst(source, ex)
x == y

