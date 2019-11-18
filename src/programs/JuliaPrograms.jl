""" Morphisms as Julia programs.

This module allows morphisms in a symmetric monoidal category to be converted to
and from programs in a subset of the Julia language.
"""
module JuliaPrograms
export Block, CompileState, compile, compile_expr, compile_block,
  @parse_wiring_diagram, parse_wiring_diagram

using Base: invokelatest
using Compat
using Match

using ...Catlab
using ...Doctrines: ObExpr, HomExpr, dom, codom
import ...Meta: Expr0, concat_expr
using ...WiringDiagrams

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

# Parsing
#########

""" Parse a wiring diagram from Julia code.
"""
macro parse_wiring_diagram(pres, expr)
  Expr(:call, GlobalRef(JuliaPrograms, :parse_wiring_diagram),
       esc(pres), esc(Expr(:quote, expr)))
end

macro parse_wiring_diagram(pres, call, body)
  Expr(:call, GlobalRef(JuliaPrograms, :parse_wiring_diagram),
       esc(pres), esc(Expr(:quote, call)), esc(Expr(:quote, body)))
end

""" Parse a wiring diagram from a Julia function expression.
"""
function parse_wiring_diagram(pres::Presentation, expr::Expr)::WiringDiagram
  @match expr begin
    Expr(:function, [call, body]) => parse_wiring_diagram(pres, call, body)
    Expr(:->, [call, body]) => parse_wiring_diagram(pres, call, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_wiring_diagram(pres::Presentation, call::Expr0, body::Expr)::WiringDiagram
  # Parse argument names and types from call expression.
  call_args = @match call begin
    Expr(:call, [name, args...]) => args
    Expr(:tuple, args) => args
    Expr(:(::), _) => [call]
    _::Symbol => [call]
    _ => error("Invalid function signature: $call")
  end
  parsed_args = map(call_args) do arg
    @match arg begin
      Expr(:(::), [name::Symbol, type::Symbol]) => (name, type)
      _ => error("Argument $arg is not simply typed")
    end
  end
  
  # Compile...
  func_expr = compile_recording_expr(first.(parsed_args), body)
  func = eval(func_expr)
  # ...and then evaluate function that records the function calls.
  inputs = last.(parsed_args)
  @assert all(has_generator(pres, name) for name in inputs)
  diagram = WiringDiagram(inputs, empty(inputs))
  v_in, v_out = input_id(diagram), output_id(diagram)
  in_ports = [ Port(v_in, OutputPort, i) for i in eachindex(inputs) ]
  recorder = name ->
    (args...) -> record_call!(diagram, generator(pres, name), args...)
  value = invokelatest(func, recorder, in_ports...)
  
  # Add outgoing wires for return values.
  out_ports = collect_call_args(Port, [value])
  diagram.output_ports = [ port_value(diagram, port) for port in out_ports ]
  add_wires!(diagram, [
    port => Port(v_out, InputPort, i) for (i, port) in enumerate(out_ports)
  ])
  diagram
end

""" Generate a Julia function expression that will record function calls.
"""
function compile_recording_expr(args::Vector{Symbol}, body::Expr;
                                recorder::Symbol=Symbol("##recorder"))::Expr
  Expr(:function,
    Expr(:tuple, recorder, args...),
    rewrite_function_names(body) do name
      Expr(:call, recorder, QuoteNode(name))
    end)
end

""" Recursively rewrite function names in function call expressions.
"""
function rewrite_function_names(rewrite::Function, expr)
  @match expr begin
    Expr(:call, [name::Symbol, args...]) =>
      Expr(:call, rewrite(name),
           (rewrite_function_names(rewrite, arg) for arg in args)...)
    Expr(head, args) =>
      Expr(head, (rewrite_function_names(rewrite, arg) for arg in args)...)
    _ => expr
  end
end

""" Record a Julia function call as a box in a wiring diagram.
"""
function record_call!(diagram::WiringDiagram, f::HomExpr, args...)
  # Add a new box for the call.
  box = Box(f)
  v = add_box!(diagram, box)

  # Adding incoming wires.
  inputs = input_ports(box)
  arg_ports = collect_call_args(Port, args)
  @assert length(arg_ports) == length(inputs)
  add_wires!(diagram, [
    Wire(port => Port(v, InputPort, i)) for (i, port) in enumerate(arg_ports)
  ])
  
  # Return output ports.
  outputs = output_ports(box)
  return_ports = [ Port(v, OutputPort, i) for i in eachindex(outputs) ]
  make_return_value(return_ports)
end

""" Collect all arguments into vector, allowing for multiplicity.
"""
function collect_call_args(T::Type, args)::Vector
  reduce(vcat, map(args) do arg
    if isnothing(arg)  # Nullary case.
      T[]
    elseif arg isa T   # Unary case.
      [arg]
    else               # General case.
      collect(arg)
    end
  end; init=T[])
end

""" Return a zero, one, or more values, following Julia conventions.
"""
function make_return_value(values)
  if isempty(values)          # Nullary case.
    nothing
  elseif length(values) == 1  # Unary case.
    first(values)
  else
    Tuple(values)             # General case.
  end
end

end
