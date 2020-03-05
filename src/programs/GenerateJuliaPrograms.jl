""" Compile or evaluate morphisms as Julia programs.
"""
module GenerateJuliaPrograms
export Block, CompileState, compile, compile_expr, compile_block,
  evaluate, evaluate_hom

using Compat

using ...Catlab
import ...Meta: Expr0, concat_expr
using ...Doctrines: ObExpr, HomExpr, dom, codom

# Compilation
#############

""" A block of Julia code with input and output variables.
"""
struct Block
  code::Expr
  inputs::Vector{<:Expr0}
  outputs::Vector{<:Expr0}
end

""" Internal state for compilation of morphism into Julia code.
"""
abstract type CompileState end

mutable struct SimpleCompileState <: CompileState
  nvars::Int
  SimpleCompileState(; nvars::Int=0) = new(nvars)
end

""" Compile a morphism expression into a Julia function.
"""
function compile(f::HomExpr; kw...)
  eval(compile_expr(f; kw...))
end

""" Compile a morphism expression into a Julia function expression.
"""
function compile_expr(f::HomExpr; name::Symbol=Symbol(),
                      args::Vector{Symbol}=Symbol[],
                      arg_types::Vector{<:Expr0}=Symbol[])
  inputs = isempty(args) ? input_exprs(ndims(dom(f)), kind=:variables) : args
  block = compile_block(f, inputs)
  to_function_expr(block; name=name, arg_types=arg_types)
end

""" Compile a morphism expression into a block of Julia code.
"""
function compile_block(f::HomExpr, inputs::Vector)
  compile_block(f, inputs, SimpleCompileState())
end

function compile_block(f::HomExpr{:generator}, inputs::Vector,
                       state::CompileState)::Block
  nin, nout = ndims(dom(f)), ndims(codom(f))
  @assert length(inputs) == nin
  outputs = genvars(state, nout)
  
  lhs = nout == 1 ? first(outputs) : Expr(:tuple, outputs...)
  rhs = generator_expr(f, inputs, state)
  Block(Expr(:(=), lhs, rhs), inputs, outputs)
end

function compile_block(f::HomExpr{:compose}, inputs::Vector,
                       state::CompileState)::Block
  code = Expr(:block)
  vars = inputs
  for g in args(f)
    block = compile_block(g, vars, state)
    code = concat_expr(code, block.code)
    vars = block.outputs
  end
  outputs = vars
  Block(code, inputs, outputs)
end

function compile_block(f::HomExpr{:id}, inputs::Vector,
                       state::CompileState)::Block
  Block(Expr(:block), inputs, inputs)
end

function compile_block(f::HomExpr{:otimes}, inputs::Vector,
                       state::CompileState)::Block
  code = Expr(:block)
  outputs = empty(inputs)
  i = 1
  for g in args(f)
    nin = ndims(dom(g))
    block = compile_block(g, inputs[i:i+nin-1], state)
    code = concat_expr(code, block.code)
    append!(outputs, block.outputs)
    i += nin
  end
  Block(code, inputs, outputs)
end

function compile_block(f::HomExpr{:braid}, inputs::Vector,
                       state::CompileState)::Block
  m = ndims(first(f))
  outputs = [inputs[m+1:end]; inputs[1:m]]
  Block(Expr(:block), inputs, outputs)
end

function compile_block(f::HomExpr{:mcopy}, inputs::Vector,
                       state::CompileState)::Block
  reps = div(ndims(codom(f)), ndims(dom(f)))
  outputs = reduce(vcat, fill(inputs, reps))
  Block(Expr(:block), inputs, outputs)
end

function compile_block(f::HomExpr{:delete}, inputs::Vector,
                       state::CompileState)::Block
  Block(Expr(:block), inputs, empty(inputs))
end

""" Convert a block of Julia code into a Julia function expression.
"""
function to_function_expr(block::Block; name::Symbol=Symbol(),
                          arg_types::Vector{<:Expr0}=Symbol[],
                          kwargs::Vector{<:Expr0}=Symbol[])
  # Create list of call arguments.
  args = block.inputs
  if !isempty(arg_types)
    @assert length(args) == length(arg_types)
    args = [ Expr(:(::), arg, type) for (arg, type) in zip(args, arg_types) ]
  end
  if !isempty(kwargs)
    kwargs = [ (kw isa Expr ? kw : Expr(:kw, kw, nothing)) for kw in kwargs ]
    args = [ Expr(:parameters, kwargs...); args ]
  end
  
  # Create call expression (function header).
  call_expr = if name == Symbol() # Anonymous function
    Expr(:tuple, args...)
  else # Named function
    Expr(:call, name, args...)
  end
  
  # Create function body.
  return_expr = Expr(:return, if length(block.outputs) == 1
    block.outputs[1]
  else
    Expr(:tuple, block.outputs...)
  end)
  body_expr = concat_expr(block.code, return_expr)
  
  Expr(:function, call_expr, body_expr)
end

""" Generate Julia expression for evaluation of morphism generator.
"""
function generator_expr(f::HomExpr{:generator}, inputs::Vector,
                        state::CompileState)
  # By default, treat even nullary generators as functions, not constants.
  value = first(f)
  Expr(:call, value::Symbol, inputs...)
end

""" Generate expressions for inputs to Julia code.
"""
function input_exprs(n::Int; kind::Symbol=:variables, prefix::Symbol=:x)
  if kind == :variables
    [ Symbol(string(prefix, i)) for i in 1:n ]
  elseif kind == :array
    [ :($prefix[$i]) for i in 1:n ]
  else
    error("Unknown input kind: $kind")
  end
end

""" Generate a fresh variable (symbol).

This is basically `gensym` with local, not global, symbol counting.
"""
function genvar(state::CompileState; prefix::Symbol=:v)::Symbol
  Symbol(string(prefix, state.nvars += 1))
end
function genvars(state::CompileState, n::Int; prefix::Symbol=:v)::Vector{Symbol}
  Symbol[ genvar(state; prefix=prefix) for i in 1:n ]
end

# Evaluation
############

""" Evaluate a morphism as a function.

If the morphism will be evaluated only once (possibly with vectorized inputs),
then direct evaluation will be much faster than compiling (via `compile`) and
evaluating a standard Julia function.

Compare with [`functor`](@ref).
"""
function evaluate(f::HomExpr, xs...; kw...)
  make_return_value(evaluate_hom(f, collect(xs); kw...))
end

function evaluate_hom(f::HomExpr{:generator}, xs::Vector;
                      generators::AbstractDict=Dict(), broadcast::Bool=false)
  fun = generators[first(f)]
  y = broadcast ? fun.(xs...) : fun(xs...)
  y isa Tuple ? collect(y) : [y]
end

function evaluate_hom(f::HomExpr{:compose}, xs::Vector; kw...)
  foldl((ys, g) -> evaluate_hom(g, ys; kw...), args(f); init=xs)
end

function evaluate_hom(f::Union{HomExpr{:otimes},HomExpr{:oplus}}, xs::Vector; kw...)
  i = 1
  mapreduce(vcat, args(f); init=[]) do g
    m = ndims(dom(g))
    ys = evaluate_hom(g, xs[i:i+m-1]; kw...)
    i += m
    ys
  end
end

evaluate_hom(f::HomExpr{:id}, xs::Vector; kw...) = xs
evaluate_hom(f::HomExpr{:braid}, xs::Vector; kw...) = [xs[2], xs[1]]

evaluate_hom(f::HomExpr{:mcopy}, xs::Vector; kw...) = begin
  reduce(vcat, fill(xs, ndims(codom(f)) ÷ ndims(dom(f))); init=[])
end
evaluate_hom(f::HomExpr{:delete}, xs::Vector; kw...) = []

""" Return a zero, one, or more values, following Julia conventions.
"""
function make_return_value(values)
  if isempty(values)          # Nullary case.
    nothing
  elseif length(values) == 1  # Unary case.
    first(values)
  else                        # General case.
    Tuple(values)
  end
end

end
