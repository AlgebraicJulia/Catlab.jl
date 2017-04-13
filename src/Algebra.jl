""" A module for traditional computer algebra from a categorical point of view.

In a conventional computer algebra system, algebraic expressions are represented
as *trees* whose leaves are variables or constants and whose internal nodes are
arithmetic operations or elementary or special functions. The idea here is to
represent expressions as morphisms in a suitable monoidal category.
"""
module Algebra
export AlgNetwork, AlgNetworkExpr,
  compose, id, otimes, munit, mcopy, delete, plus, zero,
  compile, compile_expr

using Match

using ..GAT, ..Syntax
using ..Doctrine

# Syntax
########

""" Doctrine of *algebraic networks*

TODO: Explain

See also the doctrine of abelian bicategory of relations
(`AbelianBicategoryRelations`).
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => AlgNetwork(Ob,Hom) begin
  mcopy(A::Ob)::Hom(A,otimes(A,A))
  delete(A::Ob)::Hom(A,munit())

  plus(A::Ob)::Hom(otimes(A,A),A)
  zero(A::Ob)::Hom(munit(),A)
end

@syntax AlgNetworkExpr(ObExpr,HomExpr) AlgNetwork begin
  otimes(A::Ob, B::Ob) = associate_unit(Super.otimes(A,B), munit)
  otimes(f::Hom, g::Hom) = associate(Super.otimes(f,g))
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

# Code generation
#################

type Block
  code::Expr
  inputs::Vector{Symbol}
  outputs::Vector{Symbol}
end

""" Compile an algebraic network into a Julia function.
"""
function compile(f::AlgNetworkExpr.Hom; kw...)::Function
  eval(compile_expr(f; kw...))
end

""" Compile an algebraic network into a Julia function declaration expression.
"""
function compile_expr(f::AlgNetworkExpr.Hom;
                      name::Symbol=Symbol(), args::Vector=[])::Expr
  name = name == Symbol() ? gensym("hom") : name
  nargs = length(vec(dom(f)))
  argnames = isempty(args) ? gensyms(nargs, "x") : args
  #args = [ :($a::Float64) for a in argnames ]
  args = argnames

  block = compile_block(f, argnames)
  body = concat_block(block.code, Expr(:return, block.outputs...))
  Expr(:function, Expr(:call, name, args...), body)
end

function compile_block(f::AlgNetworkExpr.Hom{:compose}, inputs::Vector)::Block
  code = Expr(:block)
  vars = inputs
  for g in args(f)
    block = compile_block(g, vars)
    code = concat_block(code, block.code)
    vars = block.outputs
  end
  outputs = vars
  Block(code, inputs, outputs)
end

function compile_block(f::AlgNetworkExpr.Hom{:generator}, inputs::Vector)::Block
  nin, nout = length(vec(dom(f))), length(vec(codom(f)))
  @assert length(inputs) == nin
  outputs = gensyms(nout)
  
  value = first(f)
  lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
  rhs = if isa(value, Symbol)
    Expr(:call, value, inputs...)
  elseif nin == 0
    value
  elseif nin == 1
    Expr(:call, :(*), value, inputs[1])
  else
    Expr(:call, :(*), value, Expr(:vcat, inputs...))
  end
  Block(Expr(:(=), lhs, rhs), inputs, outputs)
end

function concat_block(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1, _), Expr(:block, a2, _)) => Expr(:block, [a1; a2]...)
    (Expr(:block, a1, _), _) => Expr(:block, [a1; expr2]...)
    (_, Expr(:block, a2, _)) => Expr(:block, [expr1; a2]...)
    _ => Expr(:block, expr1, expr2)
  end
end

gensyms(n::Int) = [ gensym() for i in 1:n ]
gensyms(n::Int, tag) = [ gensym(tag) for i in 1:n ]

vec(A::AlgNetworkExpr.Ob{:generator}) = [A]
vec(A::AlgNetworkExpr.Ob{:otimes}) = args(A)
vec(A::AlgNetworkExpr.Ob{:munit}) = []

end
