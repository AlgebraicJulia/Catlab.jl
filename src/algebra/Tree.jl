""" Expression trees for computer algebra.

This module is *not* an implementation of a conventional, general-purpose CAS.
There are already many outstanding CAS's. Its goals are to

- display formulas in conventional notation with free variables
- facilitate interop with existing CAS's
"""
module Tree
export Formula, head, args, first, last, show_latex, show_latex, show_sexpr

using AutoHashEquals
import Base: first, last, show
import Base.Meta: show_sexpr

import ...Syntax: head, args, show_latex

# Data types
############

""" An expression tree for computer algebra.

We call these "formulas" to avoid confusion with Julia expressions (`Expr`) and
GAT expressions (`GAT.BaseExpr`).
"""
@auto_hash_equals immutable Formula
  head::Symbol
  args::Vector
  Formula(head::Symbol, args...) = new(head, collect(args))
end
head(form::Formula) = form.head
args(form::Formula) = form.args
first(form::Formula) = first(args(form))
last(form::Formula) = last(args(form))

# Pretty-print
##############

""" Show the expression in infix notation using LaTeX math.

Does *not* include `\$` or `\\[begin|end]{equation}` delimiters.
"""
show_latex(form::Formula) = show_latex(STDOUT, form)
show_latex(io::IO, form::Formula) = show_latex_formula(io, form)

show_latex_formula(io::IO, num::Number; kw...) = print(io, num)
show_latex_formula(io::IO, sym::Symbol; kw...) = print(io, sym)
show_latex_formula(io::IO, form::Formula; kw...) =
  show_latex_formula(io, form, Val{head(form)}; kw...)

function show_latex_formula(io::IO, form::Formula, ::Type; kw...)
  if length(string(head(form))) == 1
    print(io, head(form))
  else
    print(io, "\\mathop{\\mathrm{$(head(form))}}")
  end
  print(io, "\\left(")
  join(io, [sprint(show_latex_formula, arg) for arg in args(form)], ",")
  print(io, "\\right)")
end

function show_latex_formula(io::IO, form::Formula, ::Type{Val{:+}}; kw...)
  show_latex_infix(io, form, " + "; kw...)
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:*}}; kw...)
  show_latex_infix(io, form, " \\cdot "; kw...)
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:-}}; kw...)
  @assert length(args(form)) == 2
  show_latex_infix(io, form, " - "; kw...)
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:/}}; kw...)
  @assert length(args(form)) == 2
  print(io, "\\frac{")
  show_latex_formula(io, first(form))
  print(io, "}{")
  show_latex_formula(io, last(form))
  print(io, "}")
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:^}}; kw...)
  @assert length(args(form)) == 2
  show_latex_formula(io, first(form); paren=true, kw...)
  print(io, "^{")
  show_latex_formula(io, last(form))
  print(io, "}")
end

function show_latex_infix(io::IO, form::Formula, op::String;
                          paren::Bool=false, kw...)
  show_latex_paren(io, form) = show_latex_formula(io, form; paren=true, kw...)
  if (paren) print(io, "\\left(") end
  join(io, [sprint(show_latex_paren, arg) for arg in args(form)], op)
  if (paren) print(io, "\\right)") end
end

function show(io::IO, ::MIME"text/latex", form::Formula)
  print(io, "\$")
  show_latex(io, form)
  print(io, "\$")
end

""" Show the formula as an S-expression.

Cf. the standard library function `Meta.show_sexpr`.
"""
show_sexpr(form::Formula) = show_sexpr(STDOUT, form)

function show_sexpr(io::IO, form::Formula)
  print(io, "(")
  join(io, [sprint(show, head(form));
            [sprint(show_sexpr, arg) for arg in args(form)]], " ")
  print(io, ")")
end

end
