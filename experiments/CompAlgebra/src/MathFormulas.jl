""" Formulas (expression trees) for computer algebra.

This module is *not* an implementation of a conventional, general-purpose CAS.
There are already many highly developed computer algebra systems. The
objectives are to:

- represent formulas as expression trees, whenever that is convenient
- display formulas in conventional mathematical notation with free variables
- allow interoperation with existing computer algebra systems
"""
module MathFormulas
export Formula, head, args, first, last, to_formula, to_wiring_diagram,
  show_latex, show_latex_formula, show_sexpr

import Base: first, last, show
import Base.Meta: show_sexpr

using AutoHashEquals
using Match

using Catlab
import Catlab.Meta: strip_lines
import Catlab.Syntax: head, args, show_latex
using Catlab.WiringDiagrams
import Catlab.WiringDiagrams: to_wiring_diagram

using ..AlgebraicNets
import ..AlgebraicNets: Ob, Hom, compose, id, dom, codom, otimes, munit, braid,
  mcopy, delete, mmerge, create, linear, constant, wiring, evaluate

# Data types
############

""" An expression tree for computer algebra.

We call the expression trees "formulas" to avoid confusion with Julia
expressions (`Base.Expr`) or GAT expressions (`Catlab.Syntax.GATExpr`). Usually
the operations (head symbols) are interpreted as Julia functions, e.g., `:/` is
right multiplication by the matrix pseudoinverse while `:./` is the elementwise
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
@instance AlgebraicNetTheory(NFormula, Formulas) begin
  dom(f::Formulas) = NFormula(length(f.inputs))
  codom(f::Formulas) = NFormula(length(f.terms))

  function compose(f1::Formulas, f2::Formulas)::Formulas
    replacements = Dict(zip(f2.vars, f1.terms))
    terms = [ substitute(term, replacements) for term in f2.terms ]
    Formulas(terms, f1.vars)
  end

  function id(A::NFormula)::Formulas
    vars = gensyms(A)
    Formulas(vars, vars)
  end

  munit(::Type{NFormula}) = NFormula(0)
  otimes(A::NFormula, B::NFormula) = NFormula(A.n + B.n)

  function otimes(b1::Formulas, b2::Formulas)::Formulas
    Formulas([b1.terms; b2.terms], [b1.vars; b2.vars])
  end
  function braid(A::NFormula, B::NFormula)::Formulas
    v1, v2 = gensyms(A), gensyms(B)
    Formulas([v2; v1], [v1; v2])
  end

  mcopy(A::NFormula) = mcopy(A, 2)
  mmerge(A::NFormula) = mmerge(A, 2)
  delete(A::NFormula) = Formulas([], gensyms(A))
  create(A::NFormula) = Formulas(zeros(Int, A.n), [])

  function linear(value::Any, A::NFormula, B::NFormula)::Formulas
    nin, nout = A.n, B.n
    @assert nin == 1 && nout == 1 # FIXME: Relax this.
    var = gensym()
    Formulas([Formula(:*, value, var)], [var])
  end

  function constant(x::Any, A::NFormula)::Formulas
    @assert A.n == 1
    Formulas([x], Symbol[])
  end

  function wiring(f::Any, A::NFormula, B::NFormula)::Formulas
    vars = gensyms(A)
    terms = [ [] for i in 1:B.n ]
    for (src, tgts) in (f::WiringLayer).wires
      x = vars[src]
      for (tgt, c) in tgts
        push!(terms[tgt], c == 1 ? x : Formula(:*, c, x))
      end
    end
    Formulas(map(sum_formulas, terms), vars)
  end
end

function mcopy(A::NFormula, n::Int)::Formulas
  vars = gensyms(A)
  Formulas(reduce(vcat, fill(vars, n)), vars)
end

function mmerge(A::NFormula, n::Int)::Formulas
  vars = gensyms(A.n * n)
  Formulas([sum_formulas(vars[i:A.n:end]) for i in 1:A.n], vars)
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

""" Create formula for sum of zero, one, or more terms.
"""
function sum_formulas(T::Type, terms::Vector)
  if length(terms) == 0
    zero(T)
  elseif length(terms) == 1
    terms[1]
  else
    Formula(:+, terms...)
  end
end
sum_formulas(terms::Vector) = sum_formulas(Int, terms)

""" Convert a formula, or formulas, to a wiring diagram.

The wiring diagram has an input for each symbol in `vars` and an output for
each given formula. All terminal symbols not appearing in `vars` are treated as
symbolic constants.

The algorithm creates wiring diagrams in normal form for a cartesian category,
meaning that subformulas are maximally shared (cf. `normalize_copy!` for wiring
diagrams and the congruence closure algorithm).
"""
function to_wiring_diagram(formula::Formula, vars::Vector{Symbol}; kw...)
  to_wiring_diagram([formula], vars; kw...)
end

function to_wiring_diagram(formulas::Vector{Formula}, vars::Vector{Symbol};
                           to_box::Function=to_untyped_box,
                           to_port::Function=to_untyped_port)
  diagram = WiringDiagram(map(to_port, vars), map(to_port, formulas))

  term_map = Dict{Union{Formula,Symbol},Tuple{Int,Int}}((
    var => (input_id(diagram), i) for (i, var) in enumerate(vars)
  ))
  function visit(term::Formula)
    get!(term_map, term) do
      preds = map(visit, args(term))
      v = add_box!(diagram, to_box(term))
      add_wires!(diagram, (pred => (v, i) for (i, pred) in enumerate(preds)))
      (v,1)
    end
  end
  function visit(sym::Symbol)
    get!(term_map, sym) do
      v = add_box!(diagram, to_box(sym))
      (v,1)
    end
  end
  function visit(num::Number)
    v = add_box!(diagram, to_box(num))
    (v,1)
  end

  outs = map(visit, formulas)
  add_wires!(diagram,
    (out => (output_id(diagram), i) for (i, out) in enumerate(outs)))
  diagram
end

to_untyped_box(form::Formula) =
  Box(head(form), repeat([nothing], length(args(form))), [nothing])
to_untyped_box(x) = Box(x, Nothing[], [nothing])
to_untyped_port(x) = nothing

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

# Show terminal nodes as LaTeX.

function show_latex_formula(io::IO, bool::Bool; kw...)
  print(io, bool ? "\\top" : "\\bot")
end

function show_latex_formula(io::IO, num::Number; kw...)
  if num < 0
    # Treat negative literals as compound expressions.
    show_latex_formula(io, Formula(:-, abs(num)); kw...)
  else
    print(io, isinf(num) ? "\\infty" : num)
  end
end

function show_latex_formula(io::IO, sym::Symbol; kw...)
  if sym in latex_symbol_aliases
    print(io, "\\", sym)
  else
    print(io, get(latex_symbol_table, sym) do
      length(string(sym)) == 1 ? sym : "\\mathrm{$sym}"
    end)
  end
end

# Show non-terminal nodes as LaTeX.

function show_latex_formula(io::IO, form::Formula; kw...)
  # Special case: Dispatch on special LaTeX commands (e.g., \frac).
  headsym = head(form)
  if haskey(latex_command_table, headsym)
    return show_latex_command(io, form, headsym; kw...)
  end

  # Special case: Dispatch on operators (prefix, infix, and postfix).
  nargs = length(args(form))
  if nargs == 1
    if haskey(latex_prefix_table, headsym)
      return show_latex_prefix(io, form, headsym; kw...)
    end
    if haskey(latex_postfix_table, headsym)
      return show_latex_postfix(io, form, headsym; kw...)
    end
  elseif nargs > 1
    if haskey(latex_infix_table, headsym)
      return show_latex_infix(io, form, headsym; kw...)
    end
  end

  # General case: Dispatch on head symbol as value type.
  show_latex_formula(io, form, Val{headsym}; kw...)
end

# Default LaTeX pretty-printer.

function show_latex_formula(io::IO, form::Formula, ::Type; kw...)
  show_latex_formula(io, head(form))
  print(io, "\\left(")
  join(io, [sprint(show_latex_formula, arg) for arg in args(form)], ",")
  print(io, "\\right)")
end

# Special LaTeX pretty-printers.

function show_latex_formula(io::IO, form::Formula, ::Type{Val{:^}};
                            parent_precedence::Int=typemax(Int), kw...)
  @assert length(args(form)) == 2
  precedence = 2
  latex_paren_when(io, precedence >= parent_precedence) do
    show_latex_formula(io, first(form); parent_precedence=precedence, kw...)
    print(io, "^{")
    show_latex_formula(io, last(form))
    print(io, "}")
  end
end
function show_latex_formula(io::IO, form::Formula, ::Type{Val{:.^}}; kw...)
  show_latex_formula(io, form, Val{:^}; kw...)
end

# LaTeX pretty-printers for unary and binary operators.

function show_latex_infix(io::IO, form::Formula, sym::Symbol;
                          parent_precedence::Int=typemax(Int), kw...)
  op, precedence = latex_infix_table[sym]
  sep = if isempty(op)
      any(isa(x,Number) for x in args(form)[2:end]) ? " \\cdot " : " "
    else
      " $op "
  end
  show_child = (io, form) ->
    show_latex_formula(io, form; parent_precedence=precedence, kw...)
  latex_paren_when(io, precedence >= parent_precedence) do
    join(io, [sprint(show_child, arg) for arg in args(form)], sep)
  end
end

function show_latex_prefix(io::IO, form::Formula, sym::Symbol;
                           parent_precedence::Int=typemax(Int), kw...)
  @assert length(args(form)) == 1
  op, precedence = latex_prefix_table[sym]
  latex_paren_when(io, precedence >= parent_precedence) do
    print(io, op, " ")
    show_latex_formula(io, first(form); parent_precedence=precedence, kw...)
  end
end

function show_latex_postfix(io::IO, form::Formula, sym::Symbol;
                            parent_precedence::Int=typemax(Int), kw...)
  @assert length(args(form)) == 1
  op, precedence = latex_postfix_table[sym]
  latex_paren_when(io, precedence >= parent_precedence) do
    show_latex_formula(io, first(form); parent_precedence=precedence, kw...)
    print(io, " ", op)
  end
end

function show_latex_command(io::IO, form::Formula, sym::Symbol; kw...)
  cmd = latex_command_table[sym]
  print(io, cmd, "{")
  join(io, [sprint(show_latex_formula, arg) for arg in args(form)], "}{")
  print(io, "}")
end

function latex_paren_when(f::Function, io::IO, paren::Bool)
  if (paren) print(io, "\\left(") end
  f()
  if (paren) print(io, "\\right)") end
end

# Operator precedence follows the usual conventions of mathematics.
#
# https://en.wikipedia.org/wiki/Order_of_operations
# https://rosettacode.org/wiki/Operator_precedence#Mathematica

const latex_infix_table = Dict{Symbol,Tuple{String,Int}}(
  #:^ => ("^", 2),
  #:.^ => ("^", 2),
  :* => ("", 4),
  :.* => ("", 4),
  :+ => ("+", 5),
  :- => ("-", 5),
  :(==) => ("=", 6),
  :!= => ("\\neq", 6),
  :< => ("<", 6),
  :> => (">", 6),
  :<= => ("\\leq", 6),
  :>= => ("\\geq", 6),
  :in => ("\\in", 6),
  :isa => (":", 6),
  :& => ("\\wedge", 8),
  :| => ("\\vee", 8),
  :-> => ("\\mapsto", 9),
)
const latex_prefix_table = Dict{Symbol,Tuple{String,Int}}(
  :- => ("-", 3),
  :! => ("\\neg", 3),
)
const latex_postfix_table = Dict{Symbol,Tuple{String,Int}}(
  :factorial => ("!", 2),
)

const latex_command_table = Dict{Symbol,String}(
  :/ => "\\frac",
  :./ => "\\frac",
  :binomial => "\\binom",
  :sqrt => "\\sqrt",
)
const latex_symbol_table = Dict{Symbol,String}(
  :Inf => "\\infty",
  :Int => "\\mathbb{Z}", :Integer => "\\mathbb{Z}",
  :Signed => "\\mmathbb{Z}", :Unsigned => "\\mathbb{N}",
  :Real => "\\mathbb{R}", :Complex => "\\mathbb{C}",
)
const latex_symbol_aliases = Set{Symbol}([
  :alpha, :beta, :gamma, :Gamma, :delta, :Delta, :epsilon, :varepsilon,
  :zeta, :eta, :theta, :vartheta, :Theta, :iota, :kappa, :lambda, :Lambda,
  :mu, :nu, :xi, :Xi, :pi, :Pi, :rho, :varrho, :sigma, :Sigma, :tau,
  :upsilon, :Upsilon, :phi, :varphi, :Phi, :chi, :psi, :Psi, :omega, :Omega,
  :exp, :log, :sin, :cos, :tan,
])

end
