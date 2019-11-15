""" Morphisms as Julia programs.

This module allows morphisms in a symmetric monoidal category to be converted to
and from programs in a subset of the Julia language.
"""
module JuliaPrograms
export Block, CompileState, compile, compile_expr, compile_block

using ...Catlab
using ...Doctrines: ObExpr, HomExpr, dom, codom
import ...Meta: Expr0, concat_expr

# Compilation
#############

""" A block of Julia code with input and output variables.
"""
mutable struct Block
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

""" Compile a morphism expression into a Julia function expression.
"""
function compile_expr(f::HomExpr; name::Symbol=Symbol(),
                      args::Vector{Symbol}=Symbol[])
  inputs = isempty(args) ? input_exprs(ndims(dom(f)), kind=:variables) : args
  block = compile_block(f, inputs)
  to_function_expr(block; name=name)
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
function to_function_expr(block::Block; name::Symbol=Symbol(), kwargs::Vector=[])
  # Create call expression (function header).
  arguments = if isempty(kwargs)
    block.inputs
  else
    kwargs = [ (kw isa Expr ? kw : Expr(:kw, kw, nothing)) for kw in kwargs ]
    [ Expr(:parameters, kwargs...); block.inputs ]
  end
  call_expr = if name == Symbol() # Anonymous function
    Expr(:tuple, arguments...)
  else # Named function
    Expr(:call, name, arguments...)
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

end
