# ## Parse Julia Programs 
# The purpose of this documentation is to provide a tutorial on the functionality of the ParseJuliaPrograms file.
# This tutorial will provide a brief overview on each of the functions and how a wiring diagram is parsed from
# a Julia function expression.

# ## Required Libraries to Import
using GeneralizedGenerated: mk_function
using MLStyle: @match

using GATlab
import GATlab.Util.MetaUtils: Expr0
using ...Theories: ObExpr, HomExpr, otimes, munit
using ...WiringDiagrams
using ..GenerateJuliaPrograms: make_return_value

# ## Program Macro
#
macro program(pres, exprs...)
    Expr(:call, GlobalRef(ParseJuliaPrograms, :parse_wiring_diagram),
        esc(pres), (QuoteNode(expr) for expr in exprs)...)
end

# This macro is the definition for the macro @program where it takes in the presentation and the list of ast expressions as parameters
# Expr creates an expression where :call indicates the expression is a function call and
# GlobalRef creates a reference to the function being called, 
# with ParseJuliaPrograms being the module and parse_wiring_diagram the function called.
# Esc allows the presentation to be evaluated in the context of the caller rather than the macro's scope.
# QuoteNode takes each expression from the list of ast expressions passed in to create a quoted expression.

# Syntax: @program(pres, exprs...)


# ## Parse Wiring Diagram
#
function parse_wiring_diagram(pres::Presentation, expr::Expr)::WiringDiagram
    @match expr begin
        Expr(:function, call, body) => parse_wiring_diagram(pres, call, body) 
        Expr(:->, call, body) => parse_wiring_diagram(pres, call, body)
        _ => error("Not a function or lambda expression")
    end
end


# Function expression match Expr(:function, call, body) => parse_wiring_diagram(pres, call, body)  

# Lambda expression match Expr(:->, call, body) => parse_wiring_diagram(pres, call, body) 

# This function parses a wiring diagram from a Julia function expression where it takes in the presentation and a given expression as parameters.
# and uses the @match macro to determine whether the expression is a function or lambda expression and calls a following parse_wiring_diagram function with the call and body 
# of the expression if true.

# The following parse_wiring_diagram function takes in the presentation, call and body of the expression passed in from the previous parse_wiring_diagram as parameters
# and uses pattern matching to determine the arguments of the function call.
function parse_wiring_diagram(pres::Presentation, call::Expr0, body::Expr)::WiringDiagram
    syntax_module = pres.syntax
    call_args = @match call begin
      Expr(:call, name, args...) => args
      Expr(:tuple, args...) => args
      Expr(:(::), _...) => [call]
      _::Symbol => [call]
      _ => error("Invalid function signature: $call")
    end
    parsed_args = map(call_args) do arg
      @match arg begin
        Expr(:(::), name::Symbol, type_expr::Expr0) =>
          (name, eval_type_expr(pres, syntax_module, type_expr))
        _ => error("Argument $arg is missing name or type")
      end
    end
  
    args = Symbol[ first(arg) for arg in parsed_args ]
    kwargs = make_lookup_table(pres, syntax_module, unique_symbols(body))
    func_expr = compile_recording_expr(body, args,
      kwargs = sort!(collect(keys(kwargs))))
    func = mk_function(parentmodule(syntax_module), func_expr)
  
    arg_obs = syntax_module.Ob[ last(arg) for arg in parsed_args ]
    arg_blocks = Int[ length(to_wiring_diagram(ob)) for ob in arg_obs ]
    inputs = to_wiring_diagram(otimes(arg_obs))
    diagram = WiringDiagram(inputs, munit(typeof(inputs)))
    v_in, v_out = input_id(diagram), output_id(diagram)
    arg_ports = [ Tuple(Port(v_in, OutputPort, i) for i in (stop-len+1):stop)
                  for (len, stop) in zip(arg_blocks, cumsum(arg_blocks)) ]
    recorder = f -> (args...) -> record_call!(diagram, f, args...)
    value = func(recorder, arg_ports...; kwargs...)
    
    out_ports = normalize_arguments((value,))
    add_output_ports!(diagram, [
      port_value(diagram, first(ports)) for ports in out_ports
    ])
    add_wires!(diagram, [
      port => Port(v_out, InputPort, i)
      for (i, ports) in enumerate(out_ports) for port in ports
    ])
    substitute(diagram)
end

# The function first matches call expressions to output the arguments of a function call and matches the output into name type pairs, 
# validating that arguments have a name and type using eval_type_expr.  

# Case for standard function declarations ex: f(x::T, y::U)  
"""
Expr(:call, name, args...) => args 
"""
# Case for when the function call is a tuple ex: (x::T, y::U)    
"""
Expr(:tuple, args...) => args 
"""
# Case for a single argument ex: :(x::T)  
"""
Expr(:(::), _...) => [call]  
"""
# Case for a single symbol ex: :x  
"""
_::Symbol => [call]) 
"""



# Eval_type_expr is used by parse_wiring_diagram to evaluate the expression (ex: X or otimes{X, Y}) and passes in its symbol to the generator before returning the type expression.
function eval_type_expr(pres::Presentation, syntax_module::Module, expr::Expr0)
    function _eval_type_expr(expr)
      @match expr begin
        Expr(:curly, name, args...) =>
          invoke_term(syntax_module, name, map(_eval_type_expr, args))
        name::Symbol => generator(pres, name)
        _ => error("Invalid type expression $expr")
      end
    end
    _eval_type_expr(expr)
end
  

# Afterwards, the function compiles the wiring diagram where the function first parses the arguments 
# then compiles the wiring diagram using the body of the function before making the expression a callable function
"""
args = Symbol[ first(arg) for arg in parsed_args ]  
kwargs = make_lookup_table(pres, syntax_module, unique_symbols(body))  
func_expr = compile_recording_expr(body, args, kwargs = sort!(collect(keys(kwargs))))  
func = mk_function(parentmodule(syntax_module), func_expr)
"""

# The make_lookup_table function is called to create a lookup table dictionary to store and assign names to generators or term constructors.
function make_lookup_table(pres::Presentation, syntax_module::Module, names)
    theory = syntax_module.Meta.theory
    terms = Set(nameof.(keys(theory.resolvers)))
  
    table = Dict{Symbol,Any}()
    for name in names
      if has_generator(pres, name)
        table[name] = generator(pres, name)
      elseif name in terms
        table[name] = (args...) -> invoke_term(syntax_module, name, args)
      end
    end
    table
end

# The compile_recording_expr function is called to generate a Julia function expression that records function calls
# The function takes in args input and calls a rewrite function that uses the @match macro to determine the type of expression passed in.
function compile_recording_expr(body::Expr, args::Vector{Symbol};
    kwargs::Vector{Symbol}=Symbol[],
    recorder::Symbol=Symbol("##recorder"))::Expr
  function rewrite(expr)
    @match expr begin
      Expr(:call, f, args...) =>
        Expr(:call, Expr(:call, recorder, rewrite(f)), map(rewrite, args)...)
      Expr(:curly, f, args...) =>
        Expr(:call, rewrite(f), map(rewrite, args)...)
      Expr(head, args...) => Expr(head, map(rewrite, args)...)
      _ => expr
    end
  end
  Expr(:function,
    Expr(:tuple,
      Expr(:parameters, (Expr(:kw, kw, nothing) for kw in kwargs)...),
      recorder, args...),
    rewrite(body))
end

# After compile_recording_expr rewrites the function body where curly functions are mapped to a function call (ex: f(x,y) becomes f(x,y)) 
# or ordinary functions calls are mapped to recorded calls (ex: f(x,y) becomes recorder(f, x, y)), 
# the function defintion is rewritten and returned as an AST.

# For example should the body input be:  
"""  
   y = f(x)  
   z = g(y)  
   return z  
"""

# The output would be:  
"""
function (var"##recorder", x; f = nothing, g = nothing)  
   y = (var"##recorder"(f))(x)  
   z = (var"##recorder"(g))(y)  
   return z  
end
"""

# Afterwards parse_wiring_diagram then creates a diagram to record function calls
# and sets up the input and output ports for the wiring diagram.
"""
recorder = f -> (args...) -> record_call!(diagram, f, args...)  
value = func(recorder, arg_ports...; kwargs...)
"""

# Record_call! is the function called that records the function calls in the wiring diagram
# and adds wires and output ports to the box recorded in the diagram.
function record_call!(diagram::WiringDiagram, f::HomExpr, args...)
    subdiagram = to_wiring_diagram(f)
    v = add_box!(diagram, subdiagram)
  
    inputs = input_ports(subdiagram)
    arg_ports = normalize_arguments(Tuple(args))
    @assert length(arg_ports) == length(inputs)
    add_wires!(diagram, [
      Wire(port => Port(v, InputPort, i))
      for (i, ports) in enumerate(arg_ports) for port in ports
    ])
  
    outputs = output_ports(subdiagram)
    return_ports = [ Port(v, OutputPort, i) for i in eachindex(outputs) ]
    make_return_value(return_ports)
end

# Finally, parse_wiring_diagram adds outgoing wires for the return values by normalizing the arguments given as tuples or vectors
# and adding output ports to the diagram.  
"""
out_ports = normalize_arguments((value,))  
add_output_ports!(diagram, [  
    port_value(diagram, first(ports)) for ports in out_ports  
])  
add_wires!(diagram, [  
    port => Port(v_out, InputPort, i)  
    for (i, ports) in enumerate(out_ports) for port in ports  
])
"""

# Normalize_arguments function takes in the arguments passed in and normalizes them into a tuple of vectors
# where it flattens the vector of arguments and maps the arguments to a tuple of vectors.
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