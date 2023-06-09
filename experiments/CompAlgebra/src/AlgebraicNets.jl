""" Computer algebra via monoidal categories.

In a conventional computer algebra system, algebraic expressions are represented
as *trees* whose leaves are variables or constants and whose internal nodes are
arithmetic operations or elementary or special functions. The idea here is to
represent expressions as morphisms in a monoidal category.
"""
module AlgebraicNets
export ThAlgebraicNet, AlgebraicNet, Ob, Hom, dom, codom, id, compose, ⋅, ∘,
  otimes, ⊗, munit, braid, mcopy, delete, mmerge, create, linear, constant,
  compile, compile_expr, compile_expr_vector, compile_block, evaluate

using GeneralizedGenerated: mk_function
using Match
import StaticArrays

using Catlab.GATs
using Catlab.GATs.MetaUtils: concat_expr
import Catlab.GATs: show_latex, show_unicode
using Catlab.GATs.SyntaxSystems: show_latex_infix, show_unicode_infix
using Catlab.Theories: ThMonoidalCategoryWithBidiagonals, ObExpr, HomExpr
import Catlab.Theories: Ob, Hom, dom, codom,
  id, compose, ⋅, ∘, otimes, ⊗, munit, braid, mcopy, delete, mmerge, create
using Catlab.Programs
import Catlab.Programs: compile, compile_expr, compile_block, evaluate_hom
import Catlab.Programs.GenerateJuliaPrograms: genvar, genvars, to_function_expr,
  generator_expr, input_exprs

# Syntax
########

""" Theory of *algebraic networks*

TODO: Explain
"""
@signature ThAlgebraicNet{Ob,Hom} <: ThMonoidalCategoryWithBidiagonals{Ob,Hom} begin
  linear(x::Any, A::Ob, B::Ob)::(A → B)
  constant(x::Any, A::Ob)::(munit() → A)
end

@syntax AlgebraicNet{ObExpr,HomExpr} ThAlgebraicNet begin
  # FIXME: `compose` and `otimes` should delegate to wiring layer when possible.
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(new(f,g))

  mcopy(A::Ob) = mcopy(A, 2)
  mmerge(A::Ob) = mmerge(A, 2)
end

function mcopy(A::AlgebraicNet.Ob, n::Int)
  AlgebraicNet.Hom{:mcopy}([A, n], [A, otimes(fill(A, n))])
end
function mmerge(A::AlgebraicNet.Ob, n::Int)
  AlgebraicNet.Hom{:mmerge}([A, n], [otimes(fill(A, n)), A])
end

# Compilation
#############

""" Internal state for compilation of algebraic network into Julia function.
"""
mutable struct AlgebraicNetState <: CompileState
  nvars::Int
  constants::Dict{Symbol,Int}
  constants_sym::Symbol
  AlgebraicNetState(; nvars=0, constants=Dict{Symbol,Int}(), constants_sym=Symbol()) =
    new(nvars, constants, constants_sym)
end

""" Compile an algebraic network into a Julia function.

This method of "functorial compilation" generates simple imperative code with no
optimizations. Still, the code should be fast provided the original expression
is properly factored, with no duplicate computations.
"""
function compile(f::Union{AlgebraicNet.Hom,Block};
                 return_constants::Bool=false, vector::Bool=false, kw...)
  expr, constants = vector ? compile_expr_vector(f; kw...) : compile_expr(f; kw...)
  compiled = mk_function(Main, expr)
  return_constants ? (compiled, constants) : compiled
end

""" Compile an algebraic network into a Julia function expression.

The function signature is:
  - arguments = inputs (domain) of network
  - keyword arguments = symbolic constants (coefficients) of network, if any
"""
function compile_expr(f::AlgebraicNet.Hom; args::Vector{Symbol}=Symbol[])
  inputs = isempty(args) ? input_exprs(ndims(dom(f)), kind=:variables) : args
  block, constants = compile_block(f, inputs)
  function_expr = to_function_expr(block; kwargs=constants)
  (function_expr, constants)
end

""" Compile an algebraic network into a Julia function expression.

The function signature is:
  - first argument = input vector
  - second argument = constant (coefficients) vector

Unlike `compile_expr`, this method assumes the network has a single output.
"""
function compile_expr_vector(f::AlgebraicNet.Hom; inputs_sym::Symbol=:x,
                             constants_sym::Symbol=:c)
  # Compile algebraic network in block.
  inputs = input_exprs(ndims(dom(f)), prefix=inputs_sym, kind=:array)
  block, constants = compile_block(f, inputs, constants_sym=constants_sym)

  # Create call expression (function header).
  call_expr = Expr(:tuple, inputs_sym, constants_sym)

  # Create function body.
  @assert length(block.outputs) == 1
  return_expr = Expr(:return, block.outputs[1])
  body_expr = concat_expr(block.code, return_expr)

  (Expr(:function, call_expr, body_expr), constants)
end

""" Compile an algebraic network into a block of Julia code.
"""
function compile_block(f::AlgebraicNet.Hom, inputs::Vector; kw...)::Tuple{Block,Vector}
  state = AlgebraicNetState(; kw...)
  block = compile_block(f, inputs, state)
  constants = [ k for (k,v) in sort(collect(state.constants), by=x->x[2]) ]
  return (block, constants)
end

function compile_block(f::AlgebraicNet.Hom{:linear}, inputs::Vector,
                       state::AlgebraicNetState)::Block
  nin, nout = ndims(dom(f)), ndims(codom(f))
  outputs = genvars(state, nout)
  @assert length(inputs) == nin

  value = first(f)
  if value isa Symbol
    value = genconst(state, value)
  elseif value isa AbstractMatrix
    value = Expr(:call,
      Expr(:curly, GlobalRef(StaticArrays, :SMatrix), size(value)...),
      value...)
  end
  lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
  rhs = if nin == 0
    0
  elseif nin == 1
    Expr(:call, :(*), value, inputs[1])
  else
    Expr(:call, :(*), value, Expr(:vect, inputs...))
  end
  Block(Expr(:(=), lhs, rhs), inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:constant}, inputs::Vector,
                       state::AlgebraicNetState)::Block
  @assert isempty(inputs)
  outputs = genvars(state, ndims(codom(f)))
  value = first(f)
  value = isa(value, Symbol) ? genconst(state, value) : value
  lhs = length(outputs) == 1 ? outputs[1] : Expr(:tuple, outputs...)
  Block(Expr(:(=), lhs, value), inputs, outputs)
end

# FIXME: Wiring layers are gone. Migrate to another data structure?
#=
function compile_block(f::AlgebraicNet.Hom{:wiring}, inputs::Vector,
                       state::CompileState)::Block
  nout = ndims(codom(f))
  outputs = genvars(state, nout)
  terms = [ [] for i in 1:nout ]
  for (src, tgts) in first(f).wires
    x = inputs[src]
    for (tgt, c) in tgts
      push!(terms[tgt], c == 1 ? x : Expr(:call, :(.*), c, x))
    end
  end
  code = multiple_assign_expr(outputs, map(sum_expr, terms))
  Block(code, inputs, outputs)
end
=#

function compile_block(f::AlgebraicNet.Hom{:mmerge}, inputs::Vector,
                       state::CompileState)::Block
  out = genvar(state)
  code = Expr(:(=), out, sum_expr(inputs))
  Block(code, inputs, [out])
end

function compile_block(f::AlgebraicNet.Hom{:create}, inputs::Vector,
                       state::CompileState)::Block
  nout = ndims(codom(f))
  outputs = genvars(state, nout)
  code = multiple_assign_expr(outputs, zeros(nout))
  Block(code, inputs, outputs)
end

""" Generate Julia expression for morphism generator in algebraic net.
"""
function generator_expr(f::AlgebraicNet.Hom{:generator}, inputs::Vector,
                        state::AlgebraicNetState)
  value = first(f)
  if isempty(inputs)
    # If nullary, a constant, possibly symbolic.
    isa(value, Symbol) ? genconst(state, value) : value
  else
    # Otherwise, a broadcasting function call.
    Expr(:(.), value, Expr(:tuple, inputs...))
  end
end

""" Generate Julia expression for single or multiple assignment.
"""
function multiple_assign_expr(lhs::Vector, rhs::Vector)::Expr
  @assert length(lhs) == length(rhs)
  if length(lhs) == 1
    Expr(:(=), lhs[1], rhs[1])
  else
    Expr(:(=), Expr(:tuple, lhs...), Expr(:tuple, rhs...))
  end
end

""" Generate Julia expression for sum of zero, one, or more terms.
"""
function sum_expr(T::Type, terms::Vector)
  if length(terms) == 0
    zero(T)
  elseif length(terms) == 1
    terms[1]
  else
    Expr(:call, GlobalRef(Base, :broadcast), :(+), terms...)
  end
end
sum_expr(terms::Vector) = sum_expr(Float64, terms)

""" Generate a constant (symbol or expression).

See also `gensym` and `genvar`.
"""
function genconst(state::AlgebraicNetState, name::Symbol)
  i = get!(state.constants, name, length(state.constants)+1)
  state.constants_sym == Symbol() ? name : :($(state.constants_sym)[$i])
end

# Evaluation
############

function evaluate_hom(f::AlgebraicNet.Hom{:generator}, xs::Vector; kw...)
  value = first(f)
  y = if value isa Symbol && head(dom(f)) != :munit
    # Broadcasting function call.
    getfield(Main, value).(xs...)
  else
    value
  end
  y isa Tuple ? collect(y) : [y]
end

function evaluate_hom(f::AlgebraicNet.Hom{:wiring}, xs::Vector; kw...)
  # XXX: We can't properly preallocate the y's because we don't their dims.
  ys = repeat(Any[0.0], ndims(codom(f)))
  for (src, tgts) in first(f).wires
    for (tgt, c) in tgts
      y = c * xs[src]
      ys[tgt] == 0 ? (ys[tgt] = y) : (ys[tgt] += y)
    end
  end
  ys
end

evaluate_hom(f::AlgebraicNet.Hom{:mmerge}, xs::Vector; kw...) = [.+(xs...)]
evaluate_hom(f::AlgebraicNet.Hom{:create}, xs::Vector; kw...) = zeros(ndims(codom(f)))
evaluate_hom(f::AlgebraicNet.Hom{:linear}, xs::Vector; kw...) = first(f) * xs
evaluate_hom(f::AlgebraicNet.Hom{:constant}, xs::Vector; kw...) = first(f)

# Display
#########

""" Denote composition by a semicolon ala the computer scientists.

In this context, `⋅` is too easily confused for multiplication, ` ` (space) is
too implicit, and `∘` has a right-to-left connotation.
"""
function show_latex(io::IO, expr::AlgebraicNet.Hom{:compose}; paren::Bool=false, kw...)
  show_latex_infix(io, expr, ";"; paren=paren, kw...)
end
function show_unicode(io::IO, expr::AlgebraicNet.Hom{:compose}; kw...)
  show_unicode_infix(io, expr, "; "; kw...)
end

function show_latex(io::IO, expr::AlgebraicNet.Hom{:linear}; kw...)
  print(io, "\\mathop{\\mathrm{linear}}\\left[$(first(expr))\\right]")
end
function show_unicode(io::IO, expr::AlgebraicNet.Hom{:linear}; kw...)
  print(io, "linear{$(first(expr))}")
end
function show_latex(io::IO, expr::AlgebraicNet.Hom{:constant}; kw...)
  print(io, first(expr))
end
function show_unicode(io::IO, expr::AlgebraicNet.Hom{:constant}; kw...)
  print(io, first(expr))
end

end
