""" Parse Julia programs into morphisms represented as wiring diagrams.
"""
module ParseJuliaPrograms
export @program, parse_wiring_diagram

using Base: invokelatest
using Compat
using Match

using ...Catlab
import ...Meta: Expr0
using ...Doctrines: ObExpr, HomExpr
using ...WiringDiagrams
using ..GenerateJuliaPrograms: make_return_value


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
  Expr(:call, GlobalRef(ParseJuliaPrograms, :parse_wiring_diagram),
       esc(pres), esc(Expr(:quote, expr)))
end
macro program(pres, call, body)
  Expr(:call, GlobalRef(ParseJuliaPrograms, :parse_wiring_diagram),
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
  theory = syntax_module.theory().class().theory
  terms = Set([ term.name for term in theory.terms ])

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

""" Set of all symbols occuring in a Julia expression.
"""
unique_symbols(expr::Expr) =
  reduce(union!, map(unique_symbols, expr.args); init=Set{Symbol}())
unique_symbols(x::Symbol) = Set([x])
unique_symbols(x) = Set{Symbol}()

end
