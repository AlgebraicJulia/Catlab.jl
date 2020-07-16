""" Parse relations in Julia-esque syntax into undirected wiring diagrams.
"""
module ParseRelations
export @relation, parse_relation_diagram

using Compat
using Match

using ...CategoricalAlgebra.CSets, ...Present
using ...Theories: FreeCategory
using ...WiringDiagrams.UndirectedWiringDiagrams
using ...WiringDiagrams.UndirectedWiringDiagrams: TheoryUWD, TheoryTypedUWD

# Data structures
#################

@present TheoryRelationDiagram <: TheoryUWD begin
  Name::Ob
  name::Hom(Box,Name)
  variable::Hom(Junction,Name)
end

const RelationDiagram = CSetType(
  TheoryRelationDiagram, data=[:Name],
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

RelationDiagram(nports::Int) =
  UndirectedWiringDiagram(RelationDiagram, nports,
                          name=Symbol, variable=Symbol)

@present TheoryTypedRelationDiagram <: TheoryTypedUWD begin
  Name::Ob
  name::Hom(Box,Name)
  variable::Hom(Junction,Name)
end

const TypedRelationDiagram = CSetType(
  TheoryTypedRelationDiagram, data=[:Name, :Type],
  index=[:box, :junction, :outer_junction], unique_index=[:variable])

TypedRelationDiagram(port_types::AbstractVector{Symbol}) =
  UndirectedWiringDiagram(TypedRelationDiagram, port_types,
                          name=Symbol, variable=Symbol)

# Parsing
#########

""" Parse an undirected wiring diagram from a relation in Julia-esque syntax.

Unlike the [`@program`](@ref) macro for directed wiring diagrams, this macro
fundamentally alters the usual semantics of the Julia language. Function calls
with n arguments are now interpreted as assertions that an n-ary relation holds
at a particular point. For example, the operation of composing of binary
relations R ⊆ X × Y and S ⊆ Y × Z can be represented as an undirected wiring
diagram by the macro call

```julia
@relation (x,z) where (x::X, y::Y, z::Z) begin
  R(x,y)
  S(y,z)
end
```

In general, the context in the `where` clause defines the set of junctions in
the diagram and variable sharing defines the wiring of ports to junctions.
"""
macro relation(exprs...)
  Expr(:call, GlobalRef(ParseRelations, :parse_relation_diagram),
       (QuoteNode(expr) for expr in exprs)...)
end

""" Parse an undirected wiring diagram from a relation expression.

For more information, see the corresponding macro [`@relation`](@ref).
"""
function parse_relation_diagram(expr::Expr)
  @match expr begin
    Expr(:function, [head, body]) => parse_relation_diagram(head, body)
    Expr(:->, [head, body]) => parse_relation_diagram(head, body)
    _ => error("Not a function or lambda expression")
  end
end

function parse_relation_diagram(head::Expr, body::Expr)
  @match head begin
    Expr(:where, [Expr(:tuple, args), Expr(:tuple, context)]) =>
      parse_relation_diagram(context, args, body)
    _ => error("Invalid syntax in declaration of outer ports and context")
  end
end

function parse_relation_diagram(context::AbstractVector, args::AbstractVector,
                                body::Expr)
  all_vars, all_types = parse_context(context)
  outer_vars = parse_variables(args)
  outer_vars ⊆ all_vars || error("One of variables $outer_vars is not declared")
  var_types = if isnothing(all_types) # Untyped case.
    vars -> length(vars)
  else # Typed case.
    var_type_map = Dict{Symbol,Symbol}(zip(all_vars, all_types))
    vars -> getindex.(Ref(var_type_map), vars)
  end

  # Create diagram and add outer ports and junctionsm
  UWD = isnothing(all_types) ? RelationDiagram : TypedRelationDiagram
  d = UWD(var_types(outer_vars))
  add_junctions!(d, var_types(all_vars), variable=all_vars)
  set_junction!(d, ports(d, outer=true),
                incident(d, outer_vars, :variable), outer=true)

  # Add boxes to diagram.
  for expr in Base.remove_linenums!(body).args
    name, vars = @match expr begin
      Expr(:call, [name::Symbol, vars...]) => (name, parse_variables(vars))
      _ => error("Invalid syntax in box definition $expr")
    end
    vars ⊆ all_vars || error("One of variables $vars is not declared")
    box = add_box!(d, var_types(vars), name=name)
    set_junction!(d, ports(d, box), incident(d, vars, :variable))
  end

  return d
end

function parse_context(context)
  vars = map(context) do term
    @match term begin
      Expr(:(::), [var::Symbol, type::Symbol]) => (var => type)
      var::Symbol => var
      _ => error("Invalid syntax in term $expr of context")
    end
  end
  if vars isa AbstractVector{Symbol}
    (vars, nothing)
  elseif vars isa AbstractVector{Pair{Symbol,Symbol}}
    (first.(vars), last.(vars))
  else
    error("Context $context mixes typed and untyped terms")
  end
end

parse_variables(vars) = collect(Symbol, vars)

end
