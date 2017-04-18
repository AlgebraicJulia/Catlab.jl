""" Expression trees for computer algebra.

This module is *not* an implementation of a conventional, general-purpose CAS.
There are already many outstanding CAS's. Its goals are to

- display formulas in conventional notation with free variables
- facilitate interop with existing CAS's
"""
module Tree
export Formula, head, args, first, last, to_formula,
  show_latex, show_latex, show_sexpr

using AutoHashEquals
import Base: first, last, show
import Base.Meta: show_sexpr

using ...GAT, ...Syntax, ..Network
import ..Network: gensyms, substitute, ob, hom,
  compose, id, dom, codom, otimes, opow, munit, braid,
  mcopy, delete, mmerge, create, linear, constant
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
  Formula(sexp::Tuple) = new(sexp[1],
    [ isa(x, Tuple) ? Formula(x) : x for x in sexp[2:end] ])
end
head(form::Formula) = form.head
args(form::Formula) = form.args
first(form::Formula) = first(args(form))
last(form::Formula) = last(args(form))

# Conversion
############

""" Convert algebraic network to formula.

Assumes that the network has a single output.
"""
function to_formula(f::AlgebraicNet.Hom, vars::Vector{Symbol})
  formulas = functor(f; types=Dict(:Ob => NFormula, :Hom => Formulas))
  @assert codom(formulas).n == 1
  substitute(formulas.terms[1], Dict(zip(formulas.vars, vars)))
end

immutable NFormula
  n::Int
end
immutable Formulas
  terms::Vector
  vars::Vector{Symbol}
end

@instance AlgebraicNetSignature(NFormula, Formulas) begin
  function compose(f1::Formulas, f2::Formulas)::Formulas
    replacements = Dict(zip(f2.vars, f1.terms))
    terms = [ substitute(term, replacements) for term in f2.terms ]
    Formulas(terms, f1.vars)
  end

  function id(A::NFormula)::Formulas
    vars = gensyms(A)
    Formulas(vars, vars)
  end

  dom(f::Formulas) = NFormula(length(f.inputs))
  codom(f::Formulas) = NFormula(length(f.terms))

  munit(::Type{NFormula}) = NFormula(0)
  otimes(A::NFormula, B::NFormula) = NFormula(A.n + B.n)
  
  function otimes(b1::Formulas, b2::Formulas)::Formulas
    Formulas([b1.terms; b2.terms], [b1.vars; b2.vars])
  end
  function braid(A::NFormula, B::NFormula)::Formulas
    v1, v2 = gensyms(A), gensyms(B)
    Formulas([v2; v1], [v1; v2])
  end
  
  function mcopy(A::NFormula, n::Int)::Formulas
    vars = gensyms(A)
    terms = vcat(repeated(vars, n)...)
    Formulas(terms, vars)
  end
  function delete(A::NFormula)::Formulas
    Formulas([], gensyms(A))
  end
  function mmerge(A::NFormula, n::Int)::Formulas
    @assert A.n == 1 # FIXME: Relax this.
    vars = gensyms(n)
    Formulas([Formula(:+, vars...)], vars)
  end
  function create(A::NFormula)::Formulas
    Formulas(repeated(0,A.n), [])
  end
  
  function linear(value::Any, A::NFormula, B::NFormula)::Formulas
    nin, nout = A.n, B.n
    @assert nin == 1 && nout == 1 # FIXME: Relax this.
    var = gensym()
    Formulas([Formula(:*, value, var)], [var])
  end
end

ob(::Type{NFormula}, value::Any) = NFormula(1)

function hom(value::Any, A::NFormula, B::NFormula)::Formulas
  nin, nout = A.n, B.n
  @assert nout == 1
  vars = gensyms(nin)
  term = if isa(value, Symbol) && nin >= 1
    Formula(value, vars...)
  else
    value
  end
  Formulas([term], vars)
end

""" Simultaneous substitution of variables in formula.
"""
function substitute(form::Formula, subst::Dict)
  Formula(head(form), [substitute(arg, subst) for arg in args(form)]...)
end

gensyms(A::NFormula, args...) = gensyms(A.n, args...)

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
