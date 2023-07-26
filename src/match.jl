#-------------------------------------------------------------------------------
# Musings about constructing and matching syntax trees.
#
# Essentially, we want to be able match on the `head()`.

# What if we had macros to construct expression trees for cases where
# expression literals aren't ideal?
#
# Maybe we need these for pattern matching anyway? But... child ordering is
# then implied in the API?? We want to avoid this?
#
# Syntax Ideas
#
# Rich syntax? `head => [args ...]` style
#
# @SyntaxNode ref=ex break_block => [
#     Identifier => :loop_exit,
#     _while => [
#         $(expand_condition(ex[1]))
#         break_block => [
#             Identifier => :loop_cont
#             scope_block => $(blockify(expand_forms(ex[2]))
#         ]
#     ]
# ]
#
# Function call style
#
# @syntax ref=ex break_block(
#     Identifier => :loop_exit,
#     _while(
#         $(expand_condition(ex[1])),
#         break_block(
#             Identifier => :loop_cont,
#             scope_block(
#                 $(blockify(expand_forms(ex[2])))
#             )
#         )
#     )
# )
#
# S-expression style
#
# @syntax ref=ex [break_block
#                  Identifier => :loop_exit
#                  [_while
#                    $(expand_condition(ex[1]))
#                    [break_block
#                      Identifier => :loop_cont
#                      [scope_block
#                        $(blockify(expand_forms(ex[2])))]]]]
#
#
# Trying to avoid child ordering ... could we have properties?
#
# @syntax while => [
#     cond = $cond
#     body = $body
# ]
#
# We'd want symmetry so the following works?
#
#     ex = make_some_node(...)
#     @info "condition is" ex.cond
#     @info "body is" ex.body
#
# For pattern matching, syntax exactly mirroring the constructor would be (a)
# traditional and (b) mean learning only one syntax is required
#
# What about tree components where the children really are an array?  In that
# case specifically allow accessing a `children` field?  Or `args` field?
# `block` is naturally like this. (Disallow this in other cases though!?
# Implicit child ordering should not be in the API!)
#
# What about predicates matching the head?
#
# @match ex begin
#     while => (cond=$x body=$y) begin
#         # `x` and `y` are bound here??
#     end
#     block => (children=$x) begin
#         # `x` is child list here
#     end
#     $pred => begin
#         # tested with ismatch(ex, pred) by pattern compiler??
#     end
#     _ => begin
#         # default case
#         # What is bound here? We want a binding for the whole expression?
#     end
# end
#
# Generically, the idea here is that ...
#
# @match x begin
#     a ~ (q=$u, r=$v) => begin
#         body1
#     end
#     $pred ~ (q=$u) => begin
#         body2
#     end
#     _ => begin
#         body3
#     end
# end
#
# compiles down to something like ...
#
# if tagmatch(x, matcher(typeof(x), :a))
#     u = matchfield(x, :q)
#     v = matchfield(x, :r)
#     body1
# elseif tagmatch(x, matcher(typeof(x), pred))
#     u = matchfield(x, :q)
#     body2
# else
#     body3
# end
#
# The point of this lowering is that stuff like `matcher(typeof(x), :a)` can
# probably be constant folded ... `tagmatch(tag, matcher(typeof(x), pred))`
# would end up as `pred(tag)`
#
# Should the `a` and `b` be quoted or unquoted by default??  It's often just so
# damn convenient for them to be quoted ... but then if there's tags which
# aren't valid syntax like K"." ... well that's annoying hey?!  You don't want
# to have to write $(K".") ugh!

matcher(::Type{SyntaxNode}, sym::Symbol) = convert(Kind, string(sym))
matcher(::Type{SyntaxNode}, k::Kind)     = k

function tagmatch(ex::SyntaxNode, k::Kind)
    kind(ex) == k
end

@noinline function field_not_found(ex, sym)
    throw(ArgumentError("Field $sym not found in expression of kind $(kind(ex))"))
end

function matchfield(ex::SyntaxNode, sym::Symbol)
    k = kind(ex)
    if sym === :children
        k == K"block" ? children(ex) : field_not_found(ex, sym)
    elseif sym === :condition
        k == K"while" ? ex[1] : field_not_found(ex, sym)
    elseif sym === :body
        k == K"while" ? ex[2] : field_not_found(ex, sym)
    else
        field_not_found(ex, sym)
    end
end

macro match(x, pattern_block)
    @assert Meta.isexpr(pattern_block, :block)
    conditions = []
    bodies = []
    for pattern in pattern_block.args
        pattern isa LineNumberNode && continue
        @assert Meta.isexpr(pattern, :call)
        unpacked = []
        if pattern.args[1] == :~
            tag_pattern = pattern.args[2]
            a3 = pattern.args[3]
            @assert Meta.isexpr(a3, :call) && a3.args[1] == :(=>)
            unpack = a3.args[2]
            @assert Meta.isexpr(unpack, :tuple)
            for x in unpack.args
                @assert Meta.isexpr(x, :(=))
                field_name = x.args[1]
                @assert field_name isa Symbol
                @assert Meta.isexpr(x.args[2], :$)
                var_name = x.args[2].args[1]
                @assert var_name isa Symbol
                push!(unpacked, :($(esc(var_name)) = matchfield(x, $(QuoteNode(field_name)))))
            end
            body = a3.args[3]
        elseif pattern.args[1] == :(=>)
            tag_pattern = pattern.args[2]
            body = pattern.args[3]
        else
            @assert false "Bad match pattern $pattern"
        end
        push!(conditions, :(tagmatch(x, matcher(x_type, $(esc(tag_pattern))))))
        push!(bodies, :(
            let
                $(unpacked...)
                $(esc(body))
            end
        ))
    end
    if_chain = nothing
    for (c,b) in Iterators.reverse(zip(conditions, bodies))
        if_chain = Expr(:elseif, c, b, if_chain)
    end
    if_chain = Expr(:if, if_chain.args...)
    quote
        x = $(esc(x))
        x_type = typeof(x)
        $if_chain
    end
end

