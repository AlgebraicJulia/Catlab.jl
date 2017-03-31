""" Syntax for a generalized algebraic theory (GAT).

Unlike instances of a theory, syntactic expressions don't necessarily satisfy
the equations of the theory. For example, the default syntax operations for the
`Category` theory don't form a category because they don't satisfy the category
laws, e.g.,
```
compose(f, id(A)) != compose(f)
```
Whether dependent types are enfored at runtime and whether expressions are
automatically brought to normal form depends on the particular syntax. In
general, a single theory may have many different syntaxes. The purpose of this
module to make the construction of syntax simple but flexible.
"""
module Syntax
export BaseExpr, head, args, first, last, associate

# Data types
############

""" Base type for expression in the syntax of a GAT.

We define Julia types for each *type constructor* in the theory, e.g., object,
morphism*, and 2-morphism in the theory of 2-categories. Of course, Julia's
type system does not support dependent types, so the type parameters are
incorporated in the Julia types. (They are stored as extra data in the
expression instances.)
  
The concrete types are structurally similar to the core type `Expr` in Julia.
However, the *term constructor* is represented as a type parameter, rather than
as a `head` field. This makes dispatch using Julia's type system more
convenient.
"""
abstract BaseExpr{T}

term{T}(::Type{BaseExpr{T}}) = T
head{T}(::BaseExpr{T}) = T

args(expr::BaseExpr) = expr.args
first(expr::BaseExpr) = first(args(expr))
last(expr::BaseExpr) = last(args(expr))

type_args(expr::BaseExpr) = expr.type_args

# Normal forms
##############

""" Apply associative binary operation.

Maintains the normal form `op(e1,e2,...)` where `e1`,`e2`,... are expressions
that are *not* applications of `op()`
"""
function associate{E<:BaseExpr}(op::Symbol, e1::E, e2::E)::E
  terms(expr::BaseExpr) = head(expr) == op ? args(expr) : [expr]
  E{op}([terms(e1); terms(e2)], )
end

""" Apply associative binary operation with units.

Reduces a freely generated (typed) monoid to normal form.
"""
function associate{E<:BaseExpr}(op::Symbol, unit::Symbol, e1::E, e2::E)::E
  if (head(e1) == unit) e2
  elseif (head(e2) == unit) e1
  else associate(op, e1, e2) end
end

# Pretty-print
##############

""" Show the expression as an S-expression.

The transformation is *not* one-to-one since the domains and codomains are
discarded.

Cf. the standard library function `Meta.show_sexpr`.
"""
show_sexpr(expr::BaseExpr) = show_expr(STDOUT, expr)
show_sexpr(io::IO, expr::BaseExpr) = print(io, as_sexpr(expr))

function as_sexpr(expr::BaseExpr)::String
  if head(expr) == :gen
    repr(args(expr)[1])
  else
    string("(", join([head(expr), map(as_sexpr,args(expr))...], " "), ")")
  end
end

""" Show the expression in infix notation using Unicode symbols.
"""
show_infix(expr::BaseExpr) = show_infix(STDOUT, expr)
show_infix(io::IO, expr::BaseExpr) = print(io, as_infix(expr))

function as_infix(expr::BaseExpr; paren::Bool=false)::String
  head, args = Syntax.head(expr), Syntax.args(expr)
  if head == :gen # special case: generator
    return string(args[1])
  end

  symbol = get(symbol_table_unicode, head, string(head))
  if length(symbol) <= 1 && length(args) >= 2 # case 1: infix
    result = join((as_infix(a;paren=true) for a in args), symbol)
    paren ? "($result)" : result
  elseif length(args) >= 1 # case 2: prefix
    string(symbol, "[", join(map(as_infix, args), ","), "]")
  else # degenerate case: no arguments
    symbol
  end
end

const symbol_table_unicode = Dict{Symbol,String}(
  :compose => " ",
  :otimes => "⊗",
  :unit => "I",
)

""" Show the expression in infix notation using LaTeX math.

Does *not* include `\$` or `\\[begin|end]{equation}` delimiters.
"""
show_latex(expr::BaseExpr) = show_latex(STDOUT, expr)
show_latex(io::IO, expr::BaseExpr) = print(io, as_latex(expr))

as_latex(expr::BaseExpr; kw...) = as_latex(expr, Val{head(expr)}; kw...)
as_latex(expr::BaseExpr, ::Type{Val{:gen}}; kw...) = string(first(args(expr)))

# # Category
# function as_latex(id::MorExpr, ::Type{Val{:id}}; kw...)
#   subscript("\\mathrm{id}", as_latex(dom(id)))
# end
# function as_latex(expr::MorExpr, ::Type{Val{:compose}}; paren::Bool=false, kw...)
#   binary_op(expr, " ", paren)
# end
# 
# # Monoidal category
# as_latex(::ObExpr, ::Type{Val{:unit}}; kw...) = "I"
# function as_latex(expr::BaseExpr, ::Type{Val{:otimes}}; paren::Bool=false, kw...)
#   binary_op(expr, "\\otimes", paren)
# end
# 
# # Symmetric monoidal category
# function as_latex(expr::MorExpr, ::Type{Val{:braid}}; kw...)
#   subscript("\\sigma", join(map(as_latex, args(expr)), ","))
# end
# 
# # Internal (co)monoid
# function as_latex(expr::MorExpr, ::Type{Val{:copy}}; kw...)
#   subscript("\\Delta", as_latex(dom(expr)))
# end
# function as_latex(expr::MorExpr, ::Type{Val{:delete}}; kw...)
#   subscript("e", as_latex(dom(expr)))
# end
# function as_latex(expr::MorExpr, ::Type{Val{:merge}}; kw...)
#   subscript("\\nabla", as_latex(codom(expr)))
# end
# function as_latex(expr::MorExpr, ::Type{Val{:create}}; kw...)
#   subscript("i", as_latex(codom(expr)))
# end
# 
# # Closed compact category
# function as_latex(expr::ObExpr, ::Type{Val{:dual}}; kw...)
#   supscript(as_latex(first(args(expr))), "*")
# end
# function as_latex(expr::MorExpr, ::Type{Val{:eval}}; kw...)
#   subscript("\\mathrm{ev}", as_latex(first(args(expr))))
# end
# function as_latex(expr::MorExpr, ::Type{Val{:coeval}}; kw...)
#   subscript("\\mathrm{coev}", as_latex(first(args(expr))))
# end
# 
# subscript(body::String, sub::String) = "$(body)_{$sub}"
# supscript(body::String, sup::String) = "$(body)^{$sup}"
# 
# function binary_op(expr::BaseExpr, op::String, paren::Bool)
#   sep = op == " " ? op : " $op "
#   result = join((as_latex(a;paren=true) for a in args(expr)), sep)
#   paren ? "\\left($result\\right)" : result
# end
# 
# # Dagger category
# function as_latex(expr::MorExpr, ::Type{Val{:dagger}}; kw...)
#   f = first(args(expr))
#   result = as_latex(f)
#   supscript(head(f) == :gen ? result : "\\left($result\\right)", "\\dagger")
# end

end
