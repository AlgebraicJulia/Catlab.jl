""" Computer algebra via monoidal categories.

In a conventional computer algebra system, algebraic expressions are represented
as *trees* whose leaves are variables or constants and whose internal nodes are
arithmetic operations or elementary or special functions. The idea here is to
represent expressions as morphisms in a suitable monoidal category.
"""
module Network
export AlgebraicNetSignature, AlgebraicNet, ob, hom,
  compose, id, dom, codom, otimes, opow, munit, braid,
  mcopy, delete, mmerge, create, linear, constant,
  compile, compile_expr, evaluate

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

# Compilation
#############

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
  block = functor(f; types=Dict(:Ob => NBlock, :Hom => Block))
  
  # Create function header.
  name = name == Symbol() ? gensym("hom") : name
  code = block.code
  if isempty(args)
    args = block.inputs
  else
    code = substitute(code, Dict(zip(block.inputs, args)))
  end
  call_expr = Expr(:call, name, args...)

  # Create function body.
  return_expr = Expr(:return, if length(block.outputs) == 1
    block.outputs[1]
  else 
    Expr(:tuple, block.outputs...)
  end)
  body = concat(code, return_expr)
  
  Expr(:function, call_expr, body)
end

immutable NBlock
  n::Int
end
immutable Block
  code::Expr
  inputs::Vector{Symbol}
  outputs::Vector{Symbol}
end

""" Algebraic networks realized by blocks of Julia code with input and 
output variables.

These methods should only be used with `gensym`-ed variables since they assume
that any two blocks have disjoint variables.
"""
@instance AlgebraicNetSignature(NBlock, Block) begin
  function compose(b1::Block, b2::Block)::Block
    b2 = substitute(b2, Dict(zip(b2.inputs, b1.outputs)))
    code = concat(b1.code, b2.code)
    Block(code, b1.inputs, b2.outputs)
  end

  function id(A::NBlock)::Block
    vars = gensyms(A)
    Block(Expr(:block), vars, vars)
  end

  dom(block::Block) = NBlock(length(block.inputs))
  codom(block::Block) = NBlock(length(block.outputs))

  munit(::Type{NBlock}) = NBlock(0)
  otimes(A::NBlock, B::NBlock) = NBlock(A.n + B.n)
  
  function otimes(b1::Block, b2::Block)::Block
    code = concat(b1.code, b2.code)
    Block(code, [b1.inputs; b2.inputs], [b1.outputs; b2.outputs])
  end
  function braid(A::NBlock, B::NBlock)::Block
    v1, v2 = gensyms(A), gensyms(B)
    Block(Expr(:block), [v1; v2], [v2; v1])
  end
  
  function mcopy(A::NBlock, n::Int)::Block
    inputs = gensyms(A)
    outputs = vcat(repeated(inputs, n)...)
    Block(Expr(:block), inputs, outputs)
  end
  function delete(A::NBlock)::Block
    inputs = gensyms(A)
    Block(Expr(:block), inputs, [])
  end
  function mmerge(A::NBlock, n::Int)::Block
    @assert A.n == 1 # FIXME: Relax this.
    inputs = gensyms(n)
    out = gensym()
    code = Expr(:(=), out, Expr(:call, :(+), inputs...))
    Block(code, inputs, [out])
  end
  function create(A::NBlock)::Block
    outputs = gensyms(A)
    code = Expr(:(=), Expr(:tuple, outputs...), Expr(:tuple, repeated(0,A.n)...))
    Block(code, [], outputs)
  end
  
  function linear(value::Any, A::NBlock, B::NBlock)::Block
    nin, nout, inputs, outputs = A.n, B.n, gensyms(A), gensyms(B)
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
end

ob(::Type{NBlock}, value::Any) = NBlock(1)

function hom(value::Any, A::NBlock, B::NBlock)::Block
  nin, nout, inputs, outputs = A.n, B.n, gensyms(A), gensyms(B)
  lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
  rhs = if isa(value, Symbol) && nin >= 1
    Expr(:call, value, inputs...)
  else
    nout == 1 ? value : Expr(:tuple, value...)
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
  Expr(expr.head, [substitute(arg, subst) for arg in expr.args]...)
end
substitute(sym::Symbol, subst::Dict) = get(subst, sym, sym)
substitute(x::Any, subst::Dict) = x

function substitute(block::Block, subst::Dict)
  Block(substitute(block.code, subst), 
        [substitute(arg, subst) for arg in block.inputs],
        [substitute(arg, subst) for arg in block.outputs])
end

gensyms(n::Int) = [ gensym() for i in 1:n ]
gensyms(n::Int, tag) = [ gensym(tag) for i in 1:n ]
gensyms(A::NBlock, args...) = gensyms(A.n, args...)

# Evaluation
############

""" Evaluate an algebraic network without first compiling it.

If the network will only be evaluated once (possibly with vectorized inputs),
then direct evaluation will be much faster than compiling with Julia's JIT.
"""
function evaluate(f::AlgebraicNet.Hom, xs::Vararg)
  ys = eval_impl(f, collect(xs))
  length(ys) == 1 ? ys[1] : tuple(ys...)
end

# The evaluation implementation methods use a standarized input/output format:
# a vector of the same length as the (co)domain.

function eval_impl(f::AlgebraicNet.Hom{:compose}, xs::Vector)
  foldl((ys,g) -> eval_impl(g,ys), xs, args(f))
end

function eval_impl(f::AlgebraicNet.Hom{:otimes}, xs::Vector)
  ys, i = [], 1
  for g in args(f)
    m = dim(dom(g))
    append!(ys, eval_impl(g, xs[i:i+m-1]))
    i += m
  end
  ys
end

eval_impl(f::AlgebraicNet.Hom{:id}, xs::Vector) = xs
eval_impl(f::AlgebraicNet.Hom{:braid}, xs::Vector) = [xs[2], xs[1]]
eval_impl(f::AlgebraicNet.Hom{:mcopy}, xs::Vector) = vcat(repeated(xs, last(f))...)
eval_impl(f::AlgebraicNet.Hom{:delete}, xs::Vector) = []
eval_impl(f::AlgebraicNet.Hom{:mmerge}, xs::Vector) = [ +(xs...) ]
eval_impl(f::AlgebraicNet.Hom{:create}, xs::Vector) = collect(repeated(0, dim(codom(f))))
eval_impl(f::AlgebraicNet.Hom{:linear}, xs::Vector) = first(f) * xs

function eval_impl(f::AlgebraicNet.Hom{:generator}, xs::Vector)
  value = first(f)
  result = if isa(value, Symbol) && head(dom(f)) != :munit
    getfield(Main, value)(xs...)
  else
    value
  end
  isa(result, Tuple) ? collect(result) : [ result ]
end

dim(A::AlgebraicNet.Ob{:otimes}) = length(args(A))
dim(A::AlgebraicNet.Ob{:munit}) = 0
dim(A::AlgebraicNet.Ob{:generator}) = 1

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

box(name::String, f::AlgebraicNet.Hom{:generator}) = rect(name, f; rounded=false)
box(name::String, f::AlgebraicNet.Hom{:linear}) =
  rect(name, string(first(f)), wires(dom(f)), wires(codom(f)); rounded=true)
box(name::String, f::AlgebraicNet.Hom{:mcopy}) = junction_circle(name, f; fill=false)
box(name::String, f::AlgebraicNet.Hom{:delete}) = junction_circle(name, f; fill=false)
box(name::String, f::AlgebraicNet.Hom{:mmerge}) = junction_circle(name, f; fill=true)
box(name::String, f::AlgebraicNet.Hom{:create}) = junction_circle(name, f; fill=true)

end
