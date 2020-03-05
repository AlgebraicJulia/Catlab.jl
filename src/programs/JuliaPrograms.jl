""" Morphisms as Julia programs.

This module allows morphisms in a symmetric monoidal category to be converted to
and from programs in a subset of the Julia language.
"""
module JuliaPrograms
export @program, Block, CompileState, compile, compile_expr, compile_block,
  parse_wiring_diagram

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

# Parsing
#########

""" Parse a wiring diagram from a Julia program.

For the most part, this is standard Julia but we take a few liberties with the
syntax. Products are represented as tuples. So if `x` and `y` are variables of
type \$X\$ and \$Y\$, then `(x,y)` has type \$X \\otimes Y\$. Also, both `()`
and `nothing` are interpreted as the monoidal unit \$I\$.

Unlike in standard Julia, the call expressions `f(x,y)` and `f((x,y))` are
equivalent. Consequently, given morphisms \$f: W \\to X \\otimes Y\$ and \$g: X
\\otimes Y \\to Z\$, the code

```julia
x, y = f(w)
g(x,y)
```

is equivalent to `g(f(w))`. In standard Julia, at most one of these calls to `g`
would be valid.

The diagonals (copying and deleting) are implicit in the Julia syntax: copying
is variable reuse and deleting is variable non-use. For the codiagonals (merging
and creating), a special syntax is provided, reinterpreting Julia's vector
literals. The merge of `x1` and `x2` is represented by the vector `[x1,x2]` and
creation by the empty vector `[]`. For example, `f([x1,x2])` translates to
`compose(mmerge(X),f)`.

This macro is a wrapper around [`parse_wiring_diagram`](@ref).
"""
macro program(pres, expr)
  Expr(:call, GlobalRef(JuliaPrograms, :parse_wiring_diagram),
       esc(pres), esc(Expr(:quote, expr)))
end
macro program(pres, call, body)
  Expr(:call, GlobalRef(JuliaPrograms, :parse_wiring_diagram),
       esc(pres), esc(Expr(:quote, call)), esc(Expr(:quote, body)))
end

""" Parse a wiring diagram from a Julia function expression.

The macro version of this function is [`@program`](@ref).
"""
function parse_wiring_diagram(pres::Presentation, expr::Expr)::WiringDiagram
  @match expr begin
    Expr(:function, [call, body]) => parse_wiring_diagram(pres, call, body)
    Expr(:->, [call, body]) => parse_wiring_diagram(pres, call, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_wiring_diagram(pres::Presentation, call::Expr0, body::Expr)::WiringDiagram
  # FIXME: Presentations should be uniquely associated with syntax systems.
  syntax_module = Syntax.syntax_module(first(pres.generators))
  
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
      Expr(:(::), [name::Symbol, type_expr::Expr0]) =>
        (name, eval_type_expr(pres, syntax_module, type_expr))
      _ => error("Argument $arg is missing name or type")
    end
  end
  
  # Compile...
  args = first.(parsed_args)
  kwargs = make_lookup_table(pres, syntax_module, unique_symbols(body))
  func_expr = compile_recording_expr(body, args,
    kwargs = sort!(collect(keys(kwargs))))
  func = parentmodule(syntax_module).eval(func_expr)
  
  # ...and then evaluate function that records the function calls.
  arg_obs = syntax_module.Ob[ last(arg) for arg in parsed_args ]
  arg_blocks = Int[ length(to_wiring_diagram(ob)) for ob in arg_obs ]
  inputs = to_wiring_diagram(otimes(arg_obs))
  diagram = WiringDiagram(inputs, munit(typeof(inputs)))
  v_in, v_out = input_id(diagram), output_id(diagram)
  arg_ports = [ Tuple(Port(v_in, OutputPort, i) for i in (stop-len+1):stop)
                for (len, stop) in zip(arg_blocks, cumsum(arg_blocks)) ]
  recorder = f -> (args...) -> record_call!(diagram, f, args...)
  value = invokelatest(func, recorder, arg_ports...; kwargs...)
  
  # Add outgoing wires for return values.
  out_ports = normalize_arguments((value,))
  diagram.output_ports = [
    # XXX: Inferring the output port types is not reliable.
    port_value(diagram, first(ports)) for ports in out_ports
  ]
  add_wires!(diagram, [
    port => Port(v_out, InputPort, i)
    for (i, ports) in enumerate(out_ports) for port in ports
  ])
  substitute(diagram)
end

""" Make a lookup table assigning names to generators or term constructors.
"""
function make_lookup_table(pres::Presentation, syntax_module::Module, names)
  signature = syntax_module.signature().class().signature
  terms = Set([ term.name for term in signature.terms ])
  
  table = Dict{Symbol,Any}()
  for name in names
    if has_generator(pres, name)
      table[name] = generator(pres, name)
    elseif name in terms
      table[name] = (args...) -> invoke_term(syntax_module, name, args...)
    end
  end
  table
end

""" Evaluate pseudo-Julia type expression, such as `X` or `otimes{X,Y}`.
"""
function eval_type_expr(pres::Presentation, syntax_module::Module, expr::Expr0)
  function eval(expr)
    @match expr begin
      Expr(:curly, [name, args...]) =>
        invoke_term(syntax_module, name, map(eval, args)...)
      name::Symbol => generator(pres, name)
      _ => error("Invalid type expression $expr")
    end
  end
  eval(expr)
end

""" Generate a Julia function expression that will record function calls.

Rewrites the function body so that:
  
  1. Ordinary function calls are mapped to recorded calls, e.g.,
     `f(x,y)` becomes `recorder(f,x,y)`
  2. "Curly" function calls are mapped to ordinary function calls, e.g.,
     `f{X,Y}` becomes `f(X,Y)`
"""
function compile_recording_expr(body::Expr, args::Vector{Symbol};
    kwargs::Vector{Symbol}=Symbol[],
    recorder::Symbol=Symbol("##recorder"))::Expr
  function rewrite(expr)
    @match expr begin
      Expr(:call, [f, args...]) =>
        Expr(:call, Expr(:call, recorder, rewrite(f)), map(rewrite, args)...)
      Expr(:curly, [f, args...]) =>
        Expr(:call, rewrite(f), map(rewrite, args)...)
      Expr(head, args) => Expr(head, map(rewrite, args)...)
      _ => expr
    end
  end
  Expr(:function,
    Expr(:tuple,
      Expr(:parameters, (Expr(:kw, kw, nothing) for kw in kwargs)...),
      recorder, args...),
    rewrite(body))
end

""" Record a Julia function call as a box in a wiring diagram.
"""
function record_call!(diagram::WiringDiagram, f::HomExpr, args...)
  # Add a new box, itself a wiring diagram, for the call.
  subdiagram = to_wiring_diagram(f)
  v = add_box!(diagram, subdiagram)

  # Adding incoming wires.
  inputs = input_ports(subdiagram)
  arg_ports = normalize_arguments(Tuple(args))
  @assert length(arg_ports) == length(inputs)
  add_wires!(diagram, [
    Wire(port => Port(v, InputPort, i))
    for (i, ports) in enumerate(arg_ports) for port in ports
  ])
  
  # Return output ports.
  outputs = output_ports(subdiagram)
  return_ports = [ Port(v, OutputPort, i) for i in eachindex(outputs) ]
  make_return_value(return_ports)
end

""" Normalize arguments given as (possibly nested) tuples or vectors of values.
"""
function normalize_arguments(xs::Tuple)
  mapreduce(normalize_arguments, (xs,ys) -> (xs..., ys...), xs; init=())
end
function normalize_arguments(xs::Vector)
  xss = map(normalize_arguments, flatten_vec(xs)) # Vector of lists of vectors
  if isempty(xss)
    ([],) # Degenerate case
  else
    Tuple(reduce(vcat, xs) for xs in zip(xss...))
  end
end
normalize_arguments(::Nothing) = ()
normalize_arguments(x) = ([x],)
flatten_vec(xs::Vector) = mapreduce(flatten_vec, vcat, xs; init=[])
flatten_vec(x) = [x]

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

""" Set of all symbols occuring in a Julia expression.
"""
unique_symbols(expr::Expr) =
  reduce(union!, map(unique_symbols, expr.args); init=Set{Symbol}())
unique_symbols(x::Symbol) = Set([x])
unique_symbols(x) = Set{Symbol}()

end
