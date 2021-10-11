""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the ordinary sense of category theory, not
wiring diagram.
"""
module DiagrammaticPrograms
export @graph

using MLStyle: @match

using ...Present, ...Graphs, ...CategoricalAlgebra
using ...Graphs.BasicGraphs: TheoryGraph

# Data types
############

@present TheoryNamedGraph <: TheoryGraph begin
  Name::AttrType
  vname::Attr(V, Name)
  ename::Attr(E, Name)
end

@acset_type NamedGraph(TheoryNamedGraph, index=[:src,:tgt],
                       unique_index=[:vname,:ename]) <: AbstractGraph

@present TheoryMaybeNamedGraph <: TheoryGraph begin
  VName::AttrType
  EName::AttrType
  vname::Attr(V, VName)
  ename::Attr(E, EName)
end

@acset_type _MaybeNamedGraph(TheoryMaybeNamedGraph, index=[:src,:tgt],
                             unique_index=[:vname]) <: AbstractGraph

""" Default graph type for [`@graph`](@ref) macro.

Vertex names are uniquely indexed and edge names are optional and unindexed.
"""
const MaybeNamedGraph{Name} = _MaybeNamedGraph{Name,Union{Nothing,Name}}

# Graphs
########

""" Construct a graph in a simple, declarative style.

The syntax is reminiscent of Graphviz. Each line a declares a vertex or set of
vertices, or an edge. For example, the following defines a directed triangle:

```julia
@graph begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
```

Vertices in the graph must be uniquely named, whereas edges names are optional
and need not be unique.
"""
macro graph(graph_type, body)
  :(parse_graph_dsl($(esc(graph_type)), $(Meta.quot(body))))
end
macro graph(body)
  :(parse_graph_dsl(MaybeNamedGraph{Symbol}, $(Meta.quot(body))))
end

function parse_graph_dsl(G::Type, body::Expr)
  g = G()
  body = Base.remove_linenums!(body)
  for expr in body.args
    @match expr begin
      # v
      vname::Symbol => add_vertex!(g, vname=vname)
      # u, v, ...
      Expr(:tuple, vnames...) => add_vertices!(g, length(vnames), vname=vnames)
      # u → v
      Expr(:call, :(→), u::Symbol, v::Symbol) => parse_edge!(g, u, v)
      # e : u → v # parsed by Julia as (e : u) → v
      Expr(:call, :(→), Expr(:call, :(:), e::Symbol, u::Symbol), v::Symbol) =>
        parse_edge!(g, u, v, ename=e)
      # e : (u → v)
      Expr(:call, :(:), e::Symbol, Expr(:(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      _ => error("@graph macro cannot parse line: $expr")
    end
  end
  return g
end

function parse_edge!(g, s::Symbol, t::Symbol;
                     ename::Union{Symbol,Nothing}=nothing)
  e = add_edge!(g, incident(g, s, :vname), incident(g, t, :vname))
  if has_subpart(g, :ename)
    g[e,:ename] = ename
  end
  return e
end

end
