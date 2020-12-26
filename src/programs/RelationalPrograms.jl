""" Parse relation expressions in Julia syntax into undirected wiring diagrams.
"""
module RelationalPrograms
export RelationDiagram, UntypedRelationDiagram, TypedRelationDiagram,
  @relation, parse_relation_diagram

using Compat
using MLStyle: @match

using ...CategoricalAlgebra.CSets, ...Present
using ...WiringDiagrams.UndirectedWiringDiagrams
using ...WiringDiagrams.MonoidalUndirectedWiringDiagrams:
  TheoryUntypedHypergraphDiagram, TheoryHypergraphDiagram

# Data structures
#################

@present TheoryRelationDiagram <: TheoryUntypedHypergraphDiagram begin
  VarName::Data
  variable::Attr(Junction, VarName)
end

@present TheoryTypedRelationDiagram <: TheoryHypergraphDiagram begin
  VarName::Data
  variable::Attr(Junction, VarName)
end

const RelationDiagram = AbstractACSetType(TheoryRelationDiagram)
const UntypedRelationDiagram = ACSetType(TheoryRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])
const TypedRelationDiagram = ACSetType(TheoryTypedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

@present TheoryNamedRelationDiagram <: TheoryRelationDiagram begin
  port_name::Attr(Port, VarName)
  outer_port_name::Attr(OuterPort, VarName)
end

@present TheoryTypedNamedRelationDiagram <: TheoryTypedRelationDiagram begin
  port_name::Attr(Port, VarName)
  outer_port_name::Attr(OuterPort, VarName)
end

const UntypedNamedRelationDiagram = ACSetType(TheoryNamedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])
const TypedNamedRelationDiagram = ACSetType(TheoryTypedNamedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

function RelationDiagram{Name}(ports::Int; port_names=nothing) where {Name}
  if isnothing(port_names)
    return UntypedRelationDiagram{Name,Symbol}(ports)
  end
  d = UntypedNamedRelationDiagram{Name,Symbol}(ports)
  set_subpart!(d, :outer_port_name, port_names)
  return d
end

function RelationDiagram{Name}(ports::AbstractVector{T};
                               port_names=nothing) where {T,Name}
  if isnothing(port_names)
    return TypedRelationDiagram{T,Name,Symbol}(ports)
  end
  d = TypedNamedRelationDiagram{T,Name,Symbol}(ports)
  set_subpart!(d, :outer_port_name, port_names)
  return d
end

# Relation macro
################

""" Construct an undirected wiring diagram using relation notation.

Unlike the `@program` macro for directed wiring diagrams, this macro departs
from the usual semantics of the Julia programming language. Function calls with
n arguments are now interpreted as assertions that an n-ary relation holds at a
particular point. For example, the composition of binary relations R ⊆ X × Y and
S ⊆ Y × Z can be represented as an undirected wiring diagram by the macro call

```julia
@relation (x,z) where (x::X, y::Y, z::Z) begin
  R(x,y)
  S(y,z)
end
```

In general, the context in the `where` clause defines the set of junctions in
the diagram and variable sharing defines the wiring of ports to junctions.

The ports and junctions of the diagram may be typed or untyped, and the ports
may be named or unnamed. Thus four possible types of diagrams may be returned,
with the type determined by the form of relation header:

1. Untyped, unnamed: `@relation (x,z) where (x,y,z) ...`
2. Typed, unnamed: `@relation (x,z) where (x::X, y::Y, z::Z) ...`
3. Untyped, named: `@relation (out1=x, out2=z) where (x,y,z) ...`
4. Typed, named: `@relation (out=1, out2=z) where (x::X, y::Y, z::Z) ...`
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
  # Parse variables and their types from context.
  outer_expr, all_vars, all_types = @match head begin
    Expr(:where, expr, context) => (expr, parse_relation_context(context)...)
    _ => (head, nothing, nothing)
  end
  var_types = if isnothing(all_types) # Untyped case.
    vars -> length(vars)
  else # Typed case.
    var_type_map = Dict{Symbol,Symbol}(zip(all_vars, all_types))
    vars -> getindex.(Ref(var_type_map), vars)
  end

  # Create wiring diagram and add outer ports and junctions.
  _, outer_port_names, outer_vars = parse_relation_call(outer_expr)
  isnothing(all_vars) || outer_vars ⊆ all_vars ||
    error("One of variables $outer_vars is not declared in context $all_vars")
  d = RelationDiagram{Symbol}(var_types(outer_vars),
                              port_names=outer_port_names)
  if isnothing(all_vars)
    new_vars = unique(outer_vars)
    add_junctions!(d, var_types(new_vars), variable=new_vars)
  else
    add_junctions!(d, var_types(all_vars), variable=all_vars)
  end
  set_junction!(d, ports(d, outer=true),
                incident(d, outer_vars, :variable), outer=true)

  # Add box to diagram for each relation call.
  body = Base.remove_linenums!(body)
  for expr in body.args
    name, port_names, vars = parse_relation_call(expr)
    isnothing(all_vars) || vars ⊆ all_vars ||
      error("One of variables $vars is not declared in context $all_vars")
    box = add_box!(d, var_types(vars), name=name)
    if !isnothing(port_names)
      set_subpart!(d, ports(d, box), :port_name, port_names)
    end
    if isnothing(all_vars)
      new_vars = setdiff(unique(vars), d[:variable])
      add_junctions!(d, var_types(new_vars), variable=new_vars)
    end
    set_junction!(d, ports(d, box), incident(d, vars, :variable))
  end
  return d
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
      var::Symbol => var
      _ => error("Invalid syntax in term $expr of context")
    end
  end
  if vars isa AbstractVector{Symbol}
    (vars, nothing)
  elseif vars isa AbstractVector{Pair{Symbol,Symbol}}
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
