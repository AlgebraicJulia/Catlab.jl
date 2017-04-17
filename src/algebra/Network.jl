""" Computer algebra via monoidal categories.

In a conventional computer algebra system, algebraic expressions are represented
as *trees* whose leaves are variables or constants and whose internal nodes are
arithmetic operations or elementary or special functions. The idea here is to
represent expressions as morphisms in a suitable monoidal category.
"""
module Network
export AlgebraicNetSignature, AlgebraicNet, ob, hom,
  compose, id, dom, codom, otimes, opow, munit,
  mcopy, delete, mmerge, create, linear, constant,
  compile, compile_expr

using Match

using ...GAT, ...Syntax, ...Rewrite
import ...Doctrine: SymmetricMonoidalCategory, ObExpr, HomExpr, ob, hom,
  compose, id, dom, codom, otimes, munit, mcopy, delete
import ...Diagram.TikZWiring: box, wires, rect, junction_circle
import ...Syntax: show_latex, show_unicode

# Syntax
########

""" Doctrine of *algebraic networks*

TODO: Explain

See also the doctrine of abelian bicategory of relations
(`AbelianBicategoryRelations`).
"""
@signature SymmetricMonoidalCategory(Ob,Hom) => AlgebraicNetSignature(Ob,Hom) begin
  mcopy(A::Ob, n::Int)::Hom(A,opow(A,n))
  delete(A::Ob)::Hom(A,munit())

  mmerge(A::Ob, n::Int)::Hom(opow(A,n),A)
  create(A::Ob)::Hom(munit(),A)
  linear(x::Any, A::Ob, B::Ob)::Hom(A,B)
  
  constant(x::Any, A::Ob) = hom(x, munit(Ob), A)
  opow(A::Ob, n::Int) = otimes(repeated(A,n)...)
  opow(f::Hom, n::Int) = otimes(repeated(f,n)...)
  mcopy(A::Ob) = mcopy(A,2)
  mmerge(A::Ob) = mmerge(A,2)
end

@syntax AlgebraicNet(ObExpr,HomExpr) AlgebraicNetSignature begin
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

This method of "functorial compilation" generates simple imperative code with no
optimizations. Still, it should be fast provided the original expression is
properly factored (there are no duplicated computations).
"""
function compile(f::AlgebraicNet.Hom; kw...)::Function
  eval(compile_expr(f; kw...))
end

""" Compile an algebraic network into a Julia function declaration expression.
"""
function compile_expr(f::AlgebraicNet.Hom;
                      name::Symbol=Symbol(), args::Vector=[])::Expr
  block = functor(f; types=Dict(:Ob => Int, :Hom => Block))
  
  name = name == Symbol() ? gensym("hom") : name
  code = block.code
  if isempty(args)
    args = block.inputs
  else
    code = substitute(code, Dict(zip(block.inputs, args)))
  end

  return_expr = Expr(:return, if length(block.outputs) == 1
    block.outputs[1]
  else 
    Expr(:hcat, block.outputs...)
  end)
  body = concat(code, return_expr)
  Expr(:function, Expr(:call, name, args...), body)
end

@instance AlgebraicNetSignature(Int, Block) begin

  function compose(b1::Block, b2::Block)::Block
    code = concat(b1.code, substitute(b2.code, Dict(zip(b2.inputs, b1.outputs))))
    Block(code, b1.inputs, b2.outputs)
  end

  function id(m::Int)::Block
    vars = gensyms(m)
    Block(Expr(:block), vars, vars)
  end

  dom(block::Block) = length(block.inputs)
  codom(block::Block) = length(block.outputs)

  munit(::Type{Int}) = 0
  otimes(m1::Int, m2::Int) = m1+m2
  
  function otimes(b1::Block, b2::Block)::Block
    code = concat(b1.code, b2.code)
    Block(code, [b1.inputs; b2.inputs], [b1.outputs; b2.outputs])
  end
  function braid(m1::Int, m2::Int)
    v1, v2 = gensyms(m1), gensyms(m2)
    Block(Expr(:block), [v1; v2], [v2; v1])
  end
  
  function mcopy(m::Int, n::Int)::Block
    inputs = gensyms(m)
    outputs = vcat(repeated(inputs, n)...)
    Block(Expr(:block), inputs, outputs)
  end
  function delete(m::Int)::Block
    inputs = gensyms(m)
    Block(Expr(:block), inputs, [])
  end
  function mmerge(m::Int, n::Int)::Block
    @assert m == 1 # FIXME: Relax this.
    inputs = gensyms(n)
    out = gensym()
    code = Expr(:(=), out, Expr(:call, :(+), inputs...))
    Block(code, inputs, [out])
  end
  function create(m::Int)::Block
    outputs = gensyms(m)
    code = Expr(:(=), Expr(:tuple, outputs...), Expr(:tuple, repeated(0,m)...))
    Block(code, [], outputs)
  end
  
  function linear(value::Any, nin::Int, nout::Int)::Block
    inputs, outputs = gensyms(nin), gensyms(nout)
    lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
    rhs = if nin == 0
      0
    elseif nin == 1
      Expr(:call, :(*), value, inputs[1])
    else
      Expr(:call, :(*), value, Expr(:vcat, inputs...))
    end
    Block(Expr(:(=), lhs, rhs), inputs, outputs)
  end
end

ob(::Type{Int}, value::Any) = 1

function hom(value::Any, nin::Int, nout::Int)::Block
  inputs, outputs = gensyms(nin), gensyms(nout)
  lhs = if nout == 1 
    outputs[1]
  else
    Expr(:tuple, outputs...)
  end
  rhs = if isa(value, Symbol) && nin >= 1
    Expr(:call, value, inputs...)
  else
    value
  end
  Block(Expr(:(=), lhs, rhs), inputs, outputs)
end

""" Concatenate two Julia expressions.
"""
function concat(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1, _), Expr(:block, a2, _)) => Expr(:block, [a1; a2]...)
    (Expr(:block, a1, _), _) => Expr(:block, [a1; expr2]...)
    (_, Expr(:block, a2, _)) => Expr(:block, [expr1; a2]...)
    _ => Expr(:block, expr1, expr2)
  end
end

""" Simultaneous substitution of symbols in Julia expression.
"""
function substitute(expr::Expr, subst::Dict)
  Expr(expr.head, [
    if (isa(arg, Expr)) substitute(arg, subst)
    elseif (isa(arg, Symbol)) get(subst, arg, arg)
    else arg end
    for arg in expr.args
  ]...)
end

gensyms(n::Int) = [ gensym() for i in 1:n ]
gensyms(n::Int, tag) = [ gensym(tag) for i in 1:n ]

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
  value = first(expr)
  print(io, "\\mathop{\\mathrm{linear}}\\left[$value\\right]")
end
function show_unicode(io::IO, expr::AlgebraicNet.Hom{:linear}; kw...)
  value = first(expr)
  print(io, "linear[$value]")
end

function box(name::String, f::AlgebraicNet.Hom{:generator})
  rect(name, f; rounded=false)
end
function box(name::String, f::AlgebraicNet.Hom{:linear})
  rect(name, string(first(f)), wires(dom(f)), wires(codom(f)); rounded=true)
end
function box(name::String, f::AlgebraicNet.Hom{:mcopy})
  junction_circle(name, f; fill=false)
end
function box(name::String, f::AlgebraicNet.Hom{:delete})
  junction_circle(name, f; fill=false)
end
function box(name::String, f::AlgebraicNet.Hom{:mmerge})
  junction_circle(name, f; fill=true)
end
function box(name::String, f::AlgebraicNet.Hom{:create})
  junction_circle(name, f; fill=true)
end

end
