""" Morphisms as Julia programs.

This module allows morphisms in a symmetric monoidal category to be converted to
and from programs in a subset of the Julia language.
"""
module JuliaPrograms
export Block, CompileState, compile_expr, compile_block

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

""" Generate Julia expression for evaluation of morphism generator.
"""
function generator_expr(f::HomExpr{:generator}, inputs::Vector,
                        state::CompileState)
  # By default, treat even nullary generators as functions, not constants.
  value = first(f)
  Expr(:call, value::Symbol, inputs...)
end

""" Generate a fresh variable (symbol).

This is basically `gensym` with local, not global, symbol counting.
"""
function genvar(state::CompileState)::Symbol
  Symbol(string("v", state.nvars += 1))
end
function genvars(state::CompileState, n::Int)::Vector{Symbol}
  Symbol[ genvar(state) for i in 1:n ]
end

end
