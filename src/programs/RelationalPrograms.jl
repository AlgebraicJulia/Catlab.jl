""" Parse relation expressions in Julia syntax into undirected wiring diagrams.
"""
module RelationalPrograms
export @relation, parse_relation_diagram

using MLStyle: @match

using ...ADTs.RelationTerm
using ...WiringDiagrams.RelationDiagrams


""" Construct an undirected wiring diagram using relation notation.

Unlike the `@program` macro for directed wiring diagrams, this macro departs
significantly from the usual semantics of the Julia programming language.
Function calls with ``n`` arguments are now interpreted as assertions that an
``n``-ary relation holds at a particular point. For example, the composite of
binary relations ``R ⊆ X × Y`` and ``S ⊆ Y × Z`` can be represented as an
undirected wiring diagram by the macro call

```julia
@relation (x,z) where (x::X, y::Y, z::Z) begin
  R(x,y)
  S(y,z)
end
```

In general, the context in the `where` clause defines the set of junctions in
the diagram and variable sharing defines the wiring of ports to junctions. If
the `where` clause is omitted, the set of junctions is inferred from the
variables used in the macro call.

The ports and junctions of the diagram may be typed or untyped, and the ports
may be named or unnamed. Thus, four possible types of undirected wiring diagrams
may be returned, with the type determined by the form of relation header:

1. Untyped, unnamed: `@relation (x,z) where (x,y,z) ...`
2. Typed, unnamed: `@relation (x,z) where (x::X, y::Y, z::Z) ...`
3. Untyped, named: `@relation (out1=x, out2=z) where (x,y,z) ...`
4. Typed, named: `@relation (out=1, out2=z) where (x::X, y::Y, z::Z) ...`

All four types of diagram are subtypes of [`RelationDiagram`](@ref).
"""
macro relation(exprs...)
  :(parse_relation_diagram($((QuoteNode(expr) for expr in exprs)...)))
end

""" Parse an undirected wiring diagram from a relation expression.

For more information, see the corresponding macro [`@relation`](@ref).
"""
function parse_relation_diagram(expr::Expr)
  @match expr begin
    Expr(:function, head, body) => parse_relation_diagram(head, body)
    Expr(:->, head, body) => parse_relation_diagram(head, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_relation_diagram(head::Expr, body::Expr)
  # Generate dict for storing all vars
  var_dict = Dict{Symbol, Var}()

  # Look Up Function for Vars
  lookup_var(var) = begin
    if haskey(var_dict, var)
      var_dict[var]
    else
      Untyped(var)
    end
  end

  # Parse variables and their types from context.
  outer_expr, all_vars, all_types = @match head begin
    Expr(:where, expr, context) => (expr, parse_relation_context(context)...)
    _ => (head, nothing, nothing)
  end

  # Generate Context Array and Var Dict.
  context = if isnothing(all_vars)
    []
  elseif isnothing(all_types)
    map(all_vars) do var
      v = Untyped(var)
      var_dict[var] = v
      v # Return v
    end
  else
    map(all_vars, all_types) do var, type
      v = Typed(var, type)
      var_dict[var] = v
      v # Return v
    end
  end

  # Parse outer ports
  _, outer_port_names, outer_vars = parse_relation_call(outer_expr)
  isnothing(all_vars) || outer_vars ⊆ all_vars ||
    error("One of variables $outer_vars is not declared in context $all_vars")

  # Generate Outer Ports Array
  outer_ports = isempty(outer_vars) ? [] : if isnothing(outer_port_names)
    map(outer_vars) do var
      lookup_var(var)
    end
  else
    map(outer_port_names, outer_vars) do name, var
      Kwarg(name, lookup_var(var))
    end
  end


  # Generate statements for each relation call.
  body = Base.remove_linenums!(body)
  statements = map(body.args) do expr
    name, port_names, vars = parse_relation_call(expr)
    isnothing(all_vars) || vars ⊆ all_vars ||
      error("One of variables $vars is not declared in context $all_vars")
    
    # Generate Ports Array
    ports = if isnothing(port_names)
      map(vars) do var
        lookup_var(var)
      end
    else
      map(port_names, vars) do name, var
        Kwarg(name, lookup_var(var))
      end
    end

    Statement(name, ports)
  end

  # Generate UWDExpr
  uwd = UWDExpr(outer_ports, context, statements)

  # Return constructed Relation Diagram
  return RelationTerm.construct(RelationDiagram, uwd)
end

function parse_relation_context(context)
  terms = @match context begin
    Expr(:tuple) => return (Symbol[], nothing)
    Expr(:tuple, terms...) => terms
    _ => error("Invalid syntax in relation context $context")
  end
  vars = map(terms) do term
    @match term begin
      Expr(:(::), var::Symbol, type::Symbol) => (var => type)
      Expr(:(::), var::Symbol, type::Expr) => (var => type)
      Expr(:(::), var::Symbol, type::Integer) => (var => type)
      var::Symbol => var
      _ => error("Invalid syntax in term $term of context")
    end
  end

  if vars isa AbstractVector{Symbol}
    (vars, nothing)
  elseif eltype(vars) <: Pair
    (first.(vars), last.(vars))
  else
    error("Context $context mixes typed and untyped variables")
  end

end


function parse_relation_call(call)
  @match call begin
    Expr(:call, name::Symbol, Expr(:parameters, args)) =>
      (name, parse_relation_kw_args(args)...)
    Expr(:call, name::Symbol) => (name, nothing, Symbol[])
    Expr(:call, name::Symbol, args...) =>
      (name, parse_relation_inferred_args(args)...)

    Expr(:tuple, Expr(:parameters, args...)) =>
      (nothing, parse_relation_kw_args(args)...)
    Expr(:tuple) => (nothing, nothing, Symbol[])
    Expr(:tuple, args...) => (nothing, parse_relation_inferred_args(args)...)
    Expr(:(=), args...) => (nothing, parse_relation_inferred_args([call])...)

    _ => error("Invalid syntax in relation $call")
  end
end

function parse_relation_kw_args(args)
  args = map(args) do arg
    @match arg begin
      Expr(:kw, name::Symbol, var::Symbol) => (name => var)
      _ => error("Expected name as keyword argument")
    end
  end
  (first.(args), last.(args))
end

function parse_relation_inferred_args(args)
  @assert !isempty(args) # Need at least one argument to infer named/unnamed.
  args = map(args) do arg
    @match arg begin
      Expr(:kw, name::Symbol, var::Symbol) => (name => var)
      Expr(:(=), name::Symbol, var::Symbol) => (name => var)
      var::Symbol => var
      Expr(:(::), _, _) => error("All variable types must be included in the where clause and not in the argument list")
      _ => error("Expected name as positional or keyword argument")
    end
  end
  if args isa AbstractVector{Symbol}
    (nothing, args)
  elseif args isa AbstractVector{Pair{Symbol,Symbol}}
    (first.(args), last.(args))
  else
    error("Relation mixes named and unnamed arguments $args")
  end
end

end