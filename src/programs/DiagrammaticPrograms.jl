""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the ordinary sense of category theory, not
wiring diagram.
"""
module DiagrammaticPrograms
export @graph, @category

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

""" Default graph type for [`@category`](@ref) macro and related macros.
"""
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

vertex_named(g, name) = incident(g, name, :vname)
edge_named(g, name)= incident(g, name, :ename)

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
    @match reparse_arrow(expr) begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # u → v
      Expr(:call, :(→), u::Symbol, v::Symbol) => parse_edge!(g, u, v)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      _ => error("@graph macro cannot parse line: $expr")
    end
  end
  return g
end

function parse_edge!(g, s::Symbol, t::Symbol;
                     ename::Union{Symbol,Nothing}=nothing)
  e = add_edge!(g, vertex_named(g, s), vertex_named(g, t))
  if has_subpart(g, :ename)
    g[e,:ename] = ename
  end
  return e
end

function reparse_arrow(expr)
  @match expr begin
    # `f : x → y` is parsed by Julia as `(f : x) → y`, not `f : (x → y)`.
    Expr(:call, :(→), Expr(:call, :(:), f, x), y) =>
      Expr(:call, :(:), f, Expr(:call, :(→), x, y))
    _ => expr
  end
end

# Categories
############

""" Present a category by generators and relations.

The result is a finitely presented category (`FinCat`) represented by a graph,
possibly with path equations. For example, the simplex category truncated to one
dimension is:

```julia
@category begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
```

The objects and morphisms must be uniquely named.
"""
macro category(body)
  parse_category_dsl(NamedGraph{Symbol}, body)
end

function parse_category_dsl(G::Type, body::Expr)
  g, eqs = G(), Pair[]
  body = Base.remove_linenums!(body)
  for expr in body.args
    @match reparse_arrow(expr) begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(eqs, parse_equation(g, lhs, rhs))
      _ => error("@category macro cannot parse line: $expr")
    end
  end
  isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
end

""" Given generating graph, parse equation between morphisms.
"""
parse_equation(g, lhs, rhs) = parse_hom(g, lhs) => parse_hom(g, rhs)

""" Given generating graph, parse morphism expression.
"""
function parse_hom(g, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) => mapreduce(parse, vcat, args)
      Expr(:call, :(⋅), f, g) => vcat(parse(f), parse(g))
      Expr(:call, :(∘), f, g) => vcat(parse(g), parse(f))
      Expr(:call, :id, x) => empty(Path, g, vertex_named(g, x))
      f::Symbol => Path(g, edge_named(g, f))
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

end
