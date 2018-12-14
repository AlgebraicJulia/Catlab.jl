""" Expression trees for computer algebra.

This module is *not* an implementation of a conventional, general-purpose CAS.
There are already many outstanding CAS's. Its goals are to

- display formulas in conventional notation with free variables
- facilitate interop with existing CAS's
"""
module Tree
export Formula, head, args, first, last, to_formula,
  show_latex, show_latex, show_latex_formula, show_sexpr

import Base: first, last, show
import Base.Iterators: repeated
import Base.Meta: show_sexpr

using AutoHashEquals
using Match

using ...Catlab
import ...Meta: strip_lines
import ...Syntax: head, args, show_latex
using ..Network
import ..Network: Ob, Hom, compose, id, dom, codom, otimes, opow, munit, braid,
  mcopy, delete, mmerge, create, linear, constant, evaluate

# Data types
############

""" An expression tree for computer algebra.

We call these "formulas" to avoid confusion with Julia expressions
(`Base.Expr`) and GAT expressions (`Catlab.Syntax.GATExpr`). The operations
(head symbols) are interpreted as Julia functions, e.g., `:/` is right
multiplication by the matrix pseudoinverse while `:./` is the elementwise
division.
"""
@auto_hash_equals struct Formula
  head::Symbol
  args::Vector
  Formula(head::Symbol, args...) = new(head, collect(args))
  Formula(sexp::Tuple) = new(sexp[1],
    [ x isa Tuple ? Formula(x) : x for x in sexp[2:end] ])
end
head(form::Formula) = form.head
args(form::Formula) = form.args
first(form::Formula) = first(args(form))
last(form::Formula) = last(args(form))

# Conversion
############

""" Convert Julia expression to formula.

Only a subset of the Julia syntax is supported.
"""
function to_formula(expr::Expr)
  expr_to_formula(strip_lines(expr, recurse=true))
end

function expr_to_formula(expr)
  @match expr begin
    Expr(:call, [args...]) => Formula(map(expr_to_formula, args)...)
    Expr(:->, [var::Symbol, body]) => Formula(:->, var, expr_to_formula(body))
    Expr(:&&, [args...]) => Formula(:&, map(expr_to_formula, args)...)
    Expr(:||, [args...]) => Formula(:|, map(expr_to_formula, args)...)
    Expr(:block, [arg]) => expr_to_formula(arg)
    Expr(:block, _) => error("Cannot parse multiline block as formula")
    symbol::Symbol => symbol
    literal::Number => literal
    _ => error("Cannot parse expression as formula: $expr")
  end
end

""" Convert algebraic network to formula.

Assumes that the network has a single output.
"""
function to_formula(f::AlgebraicNet.Hom, vars::Vector{Symbol})
  formulas = functor((NFormula, Formulas), f)
  @assert codom(formulas).n == 1
  substitute(formulas.terms[1], Dict(zip(formulas.vars, vars)))
end

struct NFormula
  n::Int
end
struct Formulas
  terms::Vector
  vars::Vector{Symbol}
end

""" Algebraic networks realized by formulas with free variables.

These methods should only be used with `gensym`-ed variables since they assume
that any two formulas have disjoint variables.
"""
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
  opow(A::NFormula, n::Int) = NFormula(A.n * n)
  
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

Ob(::Type{NFormula}, value::Any) = NFormula(1)

function Hom(value::Any, A::NFormula, B::NFormula)::Formulas
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

gensyms(n::Int) = [ gensym() for i in 1:n ]
gensyms(n::Int, tag) = [ gensym(tag) for i in 1:n ]
gensyms(A::NFormula, args...) = gensyms(A.n, args...)

""" Simultaneous substitution of variables in formula.
"""
function substitute(form::Formula, subst::Dict)
  Formula(head(form), [substitute(arg, subst) for arg in args(form)]...)
end

""" Simultaneous substitution of symbols in Julia expression.
"""
function substitute(expr::Expr, subst::Dict)
  Expr(expr.head, [substitute(arg, subst) for arg in expr.args]...)
end
substitute(sym::Symbol, subst::Dict) = get(subst, sym, sym)
substitute(x::Any, subst::Dict) = x

# Evaluation
############

""" Evaluate a formula, optionally with vectorization.
"""
function evaluate(form::Formula, env::Dict; vector::Bool=true)
  evaluate_formula(form, env; vector=vector)
end

function evaluate_formula(form::Formula, env::Dict; vector::Bool=true)
  f = evaluate_formula(head(form), env)
  f_args = (evaluate_formula(arg, env) for arg in args(form))
  vector ? f.(f_args...) : f(f_args...)
end

function evaluate_formula(name::Symbol, env::Dict; kw...)
  # Look up name in formula environment.
  get(env, name) do
    # Failing that, look up name as field of Julia module.
    # XXX: Should the module always be Main?
    getfield(Main, name)
  end
end

evaluate_formula(literal::Number, env; kw...) = literal

# Pretty-print
##############

function show(io::IO, form::Formula)
  print(io, "Formula(")
  join(io, [ sprint(show, x) for x in [head(form); args(form)] ], ", ")
  print(io, ")")
end

function show(io::IO, ::MIME"text/latex", form::Formula)
  print(io, "\$")
  show_latex(io, form)
  print(io, "\$")
end

""" Show the expression in infix notation using LaTeX math.

Does *not* include `\$` or `\\[begin|end]{equation}` delimiters.
"""
show_latex(form::Formula) = show_latex(stdout, form)
show_latex(io::IO, form::Formula) = show_latex_formula(io, form)

# Show terminal nodes as LaTeX.

function show_latex_formula(io::IO, bool::Bool; kw...)
  print(io, bool ? "\\top" : "\\bot")
end

function show_latex_formula(io::IO, num::Number; kw...)
  if isinf(num)
    show_latex_formula(io, num > 0 ? :Inf : Formula(:-, :Inf))
  else
    print(io, num)
  end
end

function show_latex_formula(io::IO, sym::Symbol; kw...)
  print(io, get(latex_symbol_table, sym) do
    length(string(sym)) == 1 ? sym : "\\mathrm{$sym}"
  end)
end

# Show non-terminal nodes as LaTeX.

function show_latex_formula(io::IO, form::Formula; kw...)
  # Special case: Dispatch on operators with standard print protocol.
  cmd = get(latex_command_table, head(form), nothing)
  if cmd != nothing
    return show_latex_command(io, form, cmd; kw...)
  end
  nargs = length(args(form))
  if nargs == 1
    op = get(latex_prefix_table, head(form), nothing)
    if op != nothing
      return show_latex_prefix(io, form, "$op "; kw...)
    end
    op = get(latex_postfix_table, head(form), nothing)
    if op != nothing
      return show_latex_postfix(io, form, " $op"; kw...)
    end
  elseif nargs > 1
    op = get(latex_infix_table, head(form), nothing)
    if op != nothing
      return show_latex_infix(io, form, " $op "; kw...)
    end
  end

  # General case: Dispatch on head symbol as value type.
  show_latex_formula(io, form, Val{head(form)}; kw...)
end

# Default LaTeX pretty-printer.

function show_latex_formula(io::IO, form::Formula, ::Type; kw...)
  show_latex_formula(io, head(form))
  print(io, "\\left(")
  join(io, [sprint(show_latex_formula, arg) for arg in args(form)], ",")
  print(io, "\\right)")
end

# Special LaTeX pretty-printers.

function show_latex_formula(io::IO, form::Formula, ::Type{Val{:*}}; kw...)
  op = any(isa(x,Number) for x in args(form)[2:end]) ? " \\cdot " : " "
  show_latex_infix(io, form, op; kw...)
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:.*}}; kw...)
  show_latex_formula(io, form, Val{:*}; kw...)
end

function show_latex_formula(io::IO, form::Formula, ::Type{Val{:^}};
                            paren::Bool=false, kw...)
  @assert length(args(form)) == 2
  if (paren) print(io, "\\left(") end
  show_latex_formula(io, first(form); paren=true, kw...)
  print(io, "^{")
  show_latex_formula(io, last(form))
  print(io, "}")
  if (paren) print(io, "\\right)") end
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:.^}}; kw...)
  show_latex_formula(io, form, Val{:^}; kw...)
end

# LaTeX pretty-printers for unary and binary operators.

function show_latex_infix(io::IO, form::Formula, op::String;
                          paren::Bool=false, kw...)
  show_latex_paren(io, form) = show_latex_formula(io, form; paren=true, kw...)
  if (paren) print(io, "\\left(") end
  join(io, [sprint(show_latex_paren, arg) for arg in args(form)], op)
  if (paren) print(io, "\\right)") end
end

function show_latex_prefix(io::IO, form::Formula, op::String; kw...)
  @assert length(args(form)) == 1
  print(io, op)
  show_latex_formula(io, first(form); paren=true, kw...)
end

function show_latex_postfix(io::IO, form::Formula, op::String; kw...)
  @assert length(args(form)) == 1
  show_latex_formula(io, first(form); paren=true, kw...)
  print(io, op)
end

function show_latex_command(io::IO, form::Formula, cmd::String; kw...)
  print(io, "$(cmd){")
  join(io, [sprint(show_latex_formula, arg) for arg in args(form)], "}{")
  print(io, "}")
end

const latex_infix_table = Dict{Symbol,String}(
  :+ => "+",
  :- => "-",
  :(==) => "=",
  :!= => "\\neq",
  :< => "<",
  :> => ">",
  :<= => "\\leq",
  :>= => "\\geq",
  :& => "\\wedge",
  :| => "\\vee",
  :in => "\\in",
  :isa => ":",
  :-> => "\\mapsto",
)
const latex_prefix_table = Dict{Symbol,String}(
  :- => "-",
  :! => "\\neg",
)
const latex_postfix_table = Dict{Symbol,String}(
  :factorial => "!",
)
const latex_command_table = Dict{Symbol,String}(
  :/ => "\\frac",
  :./ => "\\frac",
  :binomial => "\\binom",
  :sqrt => "\\sqrt",
)
const latex_symbol_table = Dict{Symbol,String}(
  :Inf => "\\infty",
  :pi => "\\pi",
  :sin => "\\sin", :cos => "\\cos", :tan => "\\tan",
  :exp => "\\exp", :log => "\\log",
  :Int => "\\mathbb{Z}", :Integer => "\\mathbb{Z}",
  :Signed => "\\mmathbb{Z}", :Unsigned => "\\mathbb{N}",
  :Real => "\\mathbb{R}", :Complex => "\\mathbb{C}",
)

""" Show the formula as an S-expression.

Cf. the standard library function `Meta.show_sexpr`.
"""
show_sexpr(form::Formula) = show_sexpr(stdout, form)

function show_sexpr(io::IO, form::Formula)
  print(io, "(")
  join(io, [sprint(show, head(form));
            [sprint(show_sexpr, arg) for arg in args(form)]], " ")
  print(io, ")")
end

end
