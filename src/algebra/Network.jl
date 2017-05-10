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
  Block, compile, compile_expr, compile_block, evaluate

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

""" A block of Julia code with input and output variables.
"""
type Block
  code::Expr
  inputs::Vector
  outputs::Vector
  constants::Vector{Symbol}
  Block(code, inputs, outputs; constants=Symbol[]) =
    new(code, inputs, outputs, constants)
end

""" Internal state for compilation of algebraic network into Julia function.
"""
type CompileState
  inputs::Vector
  nvars::Int
  constants::Dict{Symbol,Int}
  constants_sym::Symbol
  CompileState(inputs::Vector; nvars=0,
               constants=Dict{Symbol,Int}(), constants_sym=Symbol()) =
    new(inputs, nvars, constants, constants_sym)
end

""" Compile an algebraic network into a Julia function.

This method of "functorial compilation" generates simple imperative code with no
optimizations. Still, the code should be fast provided the original expression
is properly factored (there are no duplicated computations).
"""
function compile(f::AlgebraicNet.Hom;
                 constants::Bool=false, vector::Bool=false, kw...)
  expr, consts = vector ? compile_expr_vector(f; kw...) : compile_expr(f; kw...)
  compiled = eval(expr)
  constants ? (compiled, consts) : compiled
end

""" Compile an algebraic network into a Julia function expression.

The function signature is:
  - arguments = inputs (domain) of network
  - keyword arguments = symbolic constants (coefficients) of network, if any
"""
function compile_expr(f::AlgebraicNet.Hom; name::Symbol=Symbol(),
                      args::Vector{Symbol}=Symbol[])
  block = compile_block(f; inputs=args)
  
  # Create call expression (function header).
  kw = Expr(:parameters,
            (Expr(:kw,sym,nothing) for sym in block.constants)...)
  call_expr = if name == Symbol() # Anonymous function
    Expr(:tuple, kw, block.inputs...)
  else # Named function
    Expr(:call, name, kw, block.inputs...)
  end
  
  # Create function body.
  return_expr = Expr(:return, if length(block.outputs) == 1
    block.outputs[1]
  else 
    Expr(:tuple, block.outputs...)
  end)
  body_expr = concat_expr(block.code, return_expr)
  
  (Expr(:function, call_expr, body_expr), block.constants)
end

""" Compile an algebraic network into a Julia function expression.

The function signature is:
  - first argument = input vector
  - second argument = constant (coefficients) vector
  
Unlike `compile_expr`, this method assumes the network has a single output, and
supports gradients, Hessians, and higher order derivatives (with respect to the
coefficients) via reverse-mode automatic differentiation.
"""
function compile_expr_vector(f::AlgebraicNet.Hom; name::Symbol=Symbol(),
                             order::Int=0, allorders::Bool=true)
  block = compile_block(f; inputs=:x, constants=:coef)
  
  # Create call expression (function header).
  call_expr = if name == Symbol() # Anonymous function
    :((x::Vector), (coef::Vector))
  else # Named function
    Expr(:call, name, :(x::Vector), :(coef::Vector))
  end                           
                             
  # Create function body.
  @assert length(block.outputs) == 1
  return_expr = Expr(:return, block.outputs[1])
  body_expr = concat_expr(block.code, return_expr)
  
  # Automatic differentiation with respect to coefficients.
  if order > 0
    body_expr = rdiff(body_expr; order=order, allorders=allorders, 
                      ignore=[:x], x=Vector{Float64}, coef=Vector{Float64})
  end
  
  (Expr(:function, call_expr, body_expr), block.constants)
end

""" Compile an algebraic network into a block of Julia code.
"""
function compile_block(f::AlgebraicNet.Hom;
                       inputs::Union{Symbol,Vector}=Symbol(),
                       constants::Symbol=Symbol())::Block
  nin = dim(dom(f))
  if inputs == Symbol() || inputs == []
    inputs = [ Symbol("x$i") for i in 1:nin ]
  elseif isa(inputs, Symbol)
    inputs = [ :($inputs[$i]) for i in 1:nin ]
  else
    @assert length(inputs) == nin
  end
  
  state = CompileState(inputs, constants_sym=constants)
  block = compile_block(f, state)
  block.constants = [ k for (k,v) in sort(collect(state.constants), by=x->x[2]) ]
  return block
end

function compile_block(f::AlgebraicNet.Hom{:generator}, state::CompileState)::Block
  nin, nout = dim(dom(f)), dim(codom(f))
  inputs, outputs = state.inputs, genvars(state, nout)
  @assert length(inputs) == nin
  
  value = first(f)
  lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
  rhs = if nin == 0
    isa(value, Symbol) ? genconst(state, value) : value
  else
    Expr(:call, value, inputs...)
  end
  Block(Expr(:(=), lhs, rhs), inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:linear}, state::CompileState)::Block
  nin, nout = dim(dom(f)), dim(codom(f))
  inputs, outputs = state.inputs, genvars(state, nout)
  @assert length(inputs) == nin
  
  value = first(f)
  value = isa(value, Symbol) ? genconst(state, value) : value
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

function compile_block(f::AlgebraicNet.Hom{:compose}, state::CompileState)::Block
  code = Expr(:block)
  vars = inputs = state.inputs
  for g in args(f)
    state.inputs = vars
    block = compile_block(g, state)
    code = concat_expr(code, block.code)
    vars = block.outputs
  end
  outputs = vars
  Block(code, inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:id}, state::CompileState)::Block
  inputs = state.inputs
  Block(Expr(:block), inputs, inputs)
end

function compile_block(f::AlgebraicNet.Hom{:otimes}, state::CompileState)::Block
  code = Expr(:block)
  inputs, outputs = state.inputs, Symbol[]
  i = 1
  for g in args(f)
    nin = dim(dom(g))
    state.inputs = inputs[i:i+nin-1]
    block = compile_block(g, state)
    code = concat_expr(code, block.code)
    append!(outputs, block.outputs)
    i += nin
  end
  Block(code, inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:braid}, state::CompileState)::Block
  m = dim(first(f))
  inputs = state.inputs
  outputs = [inputs[m+1:end]; inputs[1:m]]
  Block(Expr(:block), inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:mcopy}, state::CompileState)::Block
  reps = div(dim(codom(f)), dim(dom(f)))
  inputs = state.inputs
  outputs = vcat(repeated(inputs, reps)...)
  Block(Expr(:block), inputs, outputs)
end

function compile_block(f::AlgebraicNet.Hom{:delete}, state::CompileState)::Block
  Block(Expr(:block), state.inputs, [])
end

function compile_block(f::AlgebraicNet.Hom{:mmerge}, state::CompileState)::Block
  inputs, out = state.inputs, genvar(state)
  code = Expr(:(=), out, Expr(:call, :(+), inputs...))
  Block(code, inputs, [out])
end

function compile_block(f::AlgebraicNet.Hom{:create}, state::CompileState)::Block
  nout = dim(codom(f))
  inputs, outputs = state.inputs, genvars(state, nout)
  lhs = nout == 1 ? outputs[1] : Expr(:tuple, outputs...)
  rhs = nout == 1 ? 0.0 : Expr(:tuple, repeated(0.0, nout)...)
  code = Expr(:(=), lhs, rhs)
  Block(code, inputs, outputs)
end

function concat_expr(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1, _), Expr(:block, a2, _)) => Expr(:block, [a1; a2]...)
    (Expr(:block, a1, _), _) => Expr(:block, [a1; expr2]...)
    (_, Expr(:block, a2, _)) => Expr(:block, [expr1; a2]...)
    _ => Expr(:block, expr1, expr2)
  end
end

""" Generate a fresh variable (symbol).

This is basically `gensym` with local, not global, symbol counting.
"""
function genvar(state::CompileState)::Symbol
  genvars(state,1)[1]
end
function genvars(state::CompileState, n::Int)::Vector{Symbol}
  nvars = state.nvars
  vars = [ Symbol("v$(nvars+i)") for i in 1:n ]
  state.nvars = nvars + n
  return vars
end

""" Generate a constant (symbol or expression).
"""
function genconst(state::CompileState, name::Symbol)
  i = get!(state.constants, name, length(state.constants)+1)
  state.constants_sym == Symbol() ? name : :($(state.constants_sym)[$i])
end

dim(A::AlgebraicNet.Ob{:otimes}) = length(args(A))
dim(A::AlgebraicNet.Ob{:munit}) = 0
dim(A::AlgebraicNet.Ob{:generator}) = 1

# Evaluation
############

""" Evaluate an algebraic network without first compiling it.

If the network will only be evaluated once (possibly with vectorized inputs),
then direct evaluation will be much faster than compiling with Julia's JIT.

TODO: Does not support symbolic constants.
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
