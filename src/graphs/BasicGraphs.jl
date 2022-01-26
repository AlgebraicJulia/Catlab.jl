""" Data structures for graphs, based on C-sets.

Provides the category theorist's four basic kinds of graphs: graphs (aka
directed multigraphs), symmetric graphs, reflexive graphs, and symmetric
reflexive graphs. Also defines half-edge graphs. The API generally follows that
of [LightGraphs.jl](https://github.com/JuliaGraphs/LightGraphs.jl), with some
departures due to differences between the data structures.
"""
module BasicGraphs
export HasVertices, HasGraph,
  AbstractGraph, Graph, nv, ne, src, tgt, edges, inedges, outedges, vertices,
  has_edge, has_vertex, add_edge!, add_edges!, add_vertex!, add_vertices!, add_vertices_with_indices!,
  rem_edge!, rem_edges!, rem_vertex!, rem_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors, degree, induced_subgraph,
  AbstractSymmetricGraph, SymmetricGraph, inv,
  AbstractReflexiveGraph, ReflexiveGraph, refl,
  AbstractSymmetricReflexiveGraph, SymmetricReflexiveGraph,
  AbstractHalfEdgeGraph, HalfEdgeGraph, vertex, half_edges,
  add_dangling_edge!, add_dangling_edges!,
  AbstractWeightedGraph, WeightedGraph, weight,
  AbstractSymmetricWeightedGraph, SymmetricWeightedGraph,
  from_lightgraph

import Base: inv
using Requires

using ...Present, ...CSetDataStructures, ...Theories

# Base types
############

""" Abstract type for C-sets that contain vertices.

This type encompasses C-sets where the schema C contains an object `V`
interpreted as vertices. This includes, for example, graphs and half-edge
graphs, but not bipartite graphs or wiring diagrams.
"""
@abstract_acset_type HasVertices

""" Abstract type for C-sets that contain a graph.

This type encompasses C-sets where the schema for graphs is a subcategory of C.
This includes, for example, graphs, symmetric graphs, and reflexive graphs, but
not half-edge graphs.
"""
@abstract_acset_type HasGraph <: HasVertices

# Graphs
########

@present TheoryGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

""" Abstract type for graphs, aka directed multigraphs.
"""
@abstract_acset_type AbstractGraph <: HasGraph

""" A graph, also known as a directed multigraph.
"""
@acset_type Graph(TheoryGraph, index=[:src,:tgt]) <: AbstractGraph

function (::Type{T})(nv::Int; kw...) where T <: HasVertices
  g = T()
  add_vertices!(g, nv; kw...)
  return g
end

""" Number of vertices in a graph.
"""
nv(g::HasVertices) = nparts(g, :V)

""" Number of edges in a graph, or between two vertices in a graph.

In a symmetric graph, this function counts both edges in each edge pair, so that
the number of edges in a symmetric graph is twice the number of edges in the
corresponding undirected graph (at least when the edge involution has no fixed
points).
"""
ne(g::HasGraph) = nparts(g, :E)
ne(g::HasGraph, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

""" Source vertex (vertices) of edges(s) in a graph.
"""
src(g::HasGraph, args...) = subpart(g, args..., :src)

""" Target vertex (vertices) of edges(s) in a graph.
"""
tgt(g::HasGraph, args...) = subpart(g, args..., :tgt)

""" Vertices in a graph.
"""
vertices(g::HasVertices) = parts(g, :V)

""" Edges in a graph, or between two vertices in a graph.
"""
edges(g::HasGraph) = parts(g, :E)
edges(g::HasGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

""" Edges coming out of a vertex
"""
@inline outedges(g::HasGraph, v) = incident(g, v, :src)

""" Edges coming into a vertex
"""
inedges(g::HasGraph, v) = incident(g, v, :tgt)

""" Whether the graph has the given vertex.
"""
has_vertex(g::HasVertices, v) = has_part(g, :V, v)

""" Whether the graph has the given edge, or an edge between two vertices.
"""
@inline has_edge(g::HasGraph, e) = has_part(g, :E, e)
@inline function has_edge(g::HasGraph, s::Int, t::Int)
  (1 <= s <= nv(g)) || return false
  for e in outedges(g,s)
    (tgt(g,e) == t) && return true
  end
  false
end

""" Add a vertex to a graph.
"""
add_vertex!(g::HasVertices; kw...) = add_part!(g, :V; kw...)

""" Add multiple vertices to a graph.
"""
add_vertices!(g::HasVertices, n::Int; kw...) = add_parts!(g, :V, n; kw...)

""" Add vertices with preallocated src/tgt indexes
"""
function add_vertices_with_indices!(g::HasVertices, n::Int, k::Int; kw...)
  CSetDataStructures.add_parts_with_indices!(g, :V, n, (src=k,tgt=k))
  set_subparts!(g, :V; kw...)
end

""" Add an edge to a graph.
"""
add_edge!(g::HasGraph, src::Int, tgt::Int) =
  add_part!(g, :E, (src=src, tgt=tgt))

""" Add multiple edges to a graph.
"""
function add_edges!(g::HasGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E, n, (src=srcs, tgt=tgts, kw...))
end

""" Remove a vertex from a graph.

When `keep_edges` is false (the default), all edges incident to the vertex are
also deleted. When `keep_edges` is true, incident edges are preserved but their
source/target vertices become undefined.
"""
rem_vertex!(g::HasVertices, v::Int; kw...) = rem_vertices!(g, v:v; kw...)

""" Remove multiple vertices from a graph.

Edges incident to any of the vertices are treated as in [`rem_vertex!`](@ref).
"""
function rem_vertices!(g::AbstractGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    es = flatten([incident(g, vs, :src); incident(g, vs, :tgt)])
    rem_parts!(g, :E, unique!(sort!(es)))
  end
  rem_parts!(g, :V, vs)
end
flatten(x::AbstractVector{<:AbstractVector{T}}) where T =
  reduce(vcat, x, init=T[])

""" Remove an edge from a graph.
"""
rem_edge!(g::HasGraph, e::Int) = rem_part!(g, :E, e)
rem_edge!(g::HasGraph, src::Int, tgt::Int) =
  rem_edge!(g, first(edges(g, src, tgt)))

""" Remove multiple edges from a graph.
"""
rem_edges!(g::HasGraph, es) = rem_parts!(g, :E, es)

""" Neighbors of vertex in a graph.

In a graph, this function is an alias for [`outneighbors`](@ref); in a symmetric
graph, a vertex has the same out-neighbors and as in-neighbors, so the
distinction is moot.

In the presence of multiple edges, neighboring vertices are given *with
multiplicity*. To get the unique neighbors, call `unique(neighbors(g))`.
"""
@inline neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)

""" In-neighbors of vertex in a graph.
"""
@inline inneighbors(g::AbstractGraph, v::Int) = @inbounds subpart(g, incident(g, v, :tgt), :src)

""" Out-neighbors of vertex in a graph.
"""
@inline outneighbors(g::AbstractGraph, v::Int) = @inbounds subpart(g, incident(g, v, :src), :tgt)

""" Union of in-neighbors and out-neighbors in a graph.
"""
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

degree(g,v) = length(incident(g,v,:tgt)) + length(incident(g,v,:src))

""" Subgraph induced by a set of a vertices.

The [induced subgraph](https://en.wikipedia.org/wiki/Induced_subgraph) consists
of the given vertices and all edges between vertices in this set.
"""
function induced_subgraph(g::G, vs::AbstractVector{Int}) where G <: HasGraph
  vset = Set(vs)
  length(vs) == length(vset) || error("Duplicate vertices in: $vs")
  es = Iterators.filter(Iterators.flatten(incident(g, vs, :src))) do e
    tgt(g, e) ∈ vset
  end
  sub = G()
  copy_parts!(sub, g, V=vs, E=collect(Int, es))
  sub
end

# Symmetric graphs
##################

@present TheorySymmetricGraph <: TheoryGraph begin
  inv::Hom(E,E)

  compose(inv,inv) == id(E)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

""" Abstract type for symmetric graph, possibly with data attributes.
"""
@abstract_acset_type AbstractSymmetricGraph <: HasGraph

""" A symmetric graph, or graph with an orientation-reversing edge involution.

Symmetric graphs are closely related, but not identical, to undirected graphs.
"""
@acset_type SymmetricGraph(TheorySymmetricGraph, index=[:src]) <: AbstractSymmetricGraph
# Don't index `inv` because it is self-inverse and don't index `tgt`
# because `src` contains the same information due to symmetry of graph.

""" Involution on edge(s) in a symmetric graph.
"""
inv(g::HasGraph, args...) = subpart(g, args..., :inv)

add_edge!(g::AbstractSymmetricGraph, src::Int, tgt::Int; kw...) =
  add_edges!(g, src:src, tgt:tgt; kw...)

function add_edges!(g::AbstractSymmetricGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :E)
  add_parts!(g, :E, 2n; src=vcat(srcs,tgts), tgt=vcat(tgts,srcs),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

function rem_vertices!(g::AbstractSymmetricGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    es = flatten(incident(g, vs, :src))
    rem_parts!(g, :E, unique!(sort!([es; inv(g, es)])))
  end
  # FIXME: Vertex removal is inefficient because `rem_parts!` still searches for
  # edges with given targets but `tgt` is not indexed.
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractSymmetricGraph, e::Int) = rem_edges!(g, e:e)
rem_edges!(g::AbstractSymmetricGraph, es) =
  rem_parts!(g, :E, unique!(sort!([es; inv(g, es)])))

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

# Reflexive graphs
##################

@present TheoryReflexiveGraph <: TheoryGraph begin
  refl::Hom(V,E)

  compose(refl, src) == id(V)
  compose(refl, tgt) == id(V)
end

""" Abstract type for reflexive graphs, possibly with data attributes.
"""
@abstract_acset_type AbstractReflexiveGraph <: HasGraph

""" A reflexive graph.

[Reflexive graphs](https://ncatlab.org/nlab/show/reflexive+graph) are graphs in
which every vertex has a distinguished self-loop.
"""
@acset_type ReflexiveGraph(TheoryReflexiveGraph, index=[:src,:tgt]) <: AbstractReflexiveGraph

""" Reflexive loop(s) of vertex (vertices) in a reflexive graph.
"""
refl(g::HasGraph, args...) = subpart(g, args..., :refl)

add_vertex!(g::AbstractReflexiveGraph; kw...) =
  only(add_vertices!(g, 1; kw...))

function add_vertices!(g::AbstractReflexiveGraph, n::Int; kw...)
  vs = add_parts!(g, :V, n; kw...)
  es = add_parts!(g, :E, n, src=vs, tgt=vs)
  set_subpart!(g, vs, :refl, es)
  vs
end

function rem_vertices!(g::AbstractReflexiveGraph, vs; keep_edges::Bool=false)
  es = if keep_edges
    sort(refl(g, vs)) # Always delete reflexive edges.
  else
    unique!(sort!(flatten([incident(g, vs, :src); incident(g, vs, :tgt)])))
  end
  rem_parts!(g, :E, es)
  rem_parts!(g, :V, vs)
end

# Symmetric reflexive graphs
############################

@present TheorySymmetricReflexiveGraph <: TheorySymmetricGraph begin
  refl::Hom(V,E)

  compose(refl, src) == id(V)
  compose(refl, tgt) == id(V)
  compose(refl, inv) == refl # Reflexive loop fixed by involution.
end

""" Abstract type for symmetric reflexive graphs, possibly with data attributes.
"""
@abstract_acset_type AbstractSymmetricReflexiveGraph <: HasGraph

""" A symmetric reflexive graph.

Symmetric reflexive graphs are both symmetric graphs ([`SymmetricGraph`](@ref))
and reflexive graphs ([`ReflexiveGraph`](@ref)) such that the reflexive loops
are fixed by the edge involution.
"""
@acset_type SymmetricReflexiveGraph(TheorySymmetricReflexiveGraph, index=[:src]) <:
  AbstractSymmetricReflexiveGraph

add_vertex!(g::AbstractSymmetricReflexiveGraph; kw...) =
  only(add_vertices!(g, 1; kw...))

function add_vertices!(g::AbstractSymmetricReflexiveGraph, n::Int; kw...)
  vs = add_parts!(g, :V, n; kw...)
  es = add_parts!(g, :E, n, src=vs, tgt=vs)
  set_subpart!(g, vs, :refl, es)
  set_subpart!(g, es, :inv, es)
  vs
end

add_edge!(g::AbstractSymmetricReflexiveGraph, src::Int, tgt::Int; kw...) =
  add_edges!(g, src:src, tgt:tgt; kw...)

function add_edges!(g::AbstractSymmetricReflexiveGraph,
                    srcs::AbstractVector{Int}, tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :E)
  add_parts!(g, :E, 2n; src=vcat(srcs,tgts), tgt=vcat(tgts,srcs),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

function rem_vertices!(g::AbstractSymmetricReflexiveGraph, vs;
                       keep_edges::Bool=false)
  es = if keep_edges
    sort(refl(g, vs)) # Always delete reflexive edges.
  else
    es = flatten(incident(g, vs, :src))
    unique!(sort!([es; inv(g, es)]))
  end
  rem_parts!(g, :E, es)
  # FIXME: Vertex removal is inefficient for same reason as `SymmetricGraph`.
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractSymmetricReflexiveGraph, e::Int) = rem_edges!(g, e:e)
rem_edges!(g::AbstractSymmetricReflexiveGraph, es) =
  rem_parts!(g, :E, unique!(sort!([es; inv(g, es)])))

# Half-edge graphs
##################

@present TheoryHalfEdgeGraph(FreeSchema) begin
  V::Ob
  H::Ob
  vertex::Hom(H,V)
  inv::Hom(H,H)

  compose(inv, inv) == id(H)
end

""" Abstract type for half-edge graphs, possibly with data attributes.
"""
@abstract_acset_type AbstractHalfEdgeGraph <: HasVertices

""" A half-edge graph.

[Half-edge
graphs](https://www.algebraicjulia.org/blog/post/2020/09/cset-graphs-2/) are a
variant of undirected graphs whose edges are pairs of "half-edges" or "darts".
Half-edge graphs are isomorphic to symmetric graphs but have a different data
model.
"""
@acset_type HalfEdgeGraph(TheoryHalfEdgeGraph, index=[:vertex]) <: AbstractHalfEdgeGraph

""" Incident vertex (vertices) of half-edge(s) in a half-edge graph.
"""
vertex(g::AbstractHalfEdgeGraph, args...) = subpart(g, args..., :vertex)

""" Involution on half-edge(s) in a half-edge graph.
"""
inv(g::AbstractHalfEdgeGraph, args...) = subpart(g, args..., :inv)

""" Half-edges in a half-edge graph, or incident to a vertex.
"""
half_edges(g::AbstractHalfEdgeGraph) = parts(g, :H)
half_edges(g::AbstractHalfEdgeGraph, v) = incident(g, v, :vertex)

function half_edge_pairs(g::AbstractHalfEdgeGraph, src::Int, tgt::Int)
  hs = half_edges(g, src)
  hs′ = inv(g, hs)
  has_tgt = vertex(g, hs′) .== tgt
  (hs[has_tgt], hs′[has_tgt])
end

@inline add_edge!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int; kw...) =
  add_half_edge_pair!(g, src, tgt; kw...)

@inline add_edges!(g::AbstractHalfEdgeGraph, srcs::AbstractVector{Int},
                   tgts::AbstractVector{Int}; kw...) =
  add_half_edge_pairs!(g, srcs, tgts; kw...)

function add_half_edge_pair!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int; kw...)
  k = nparts(g, :H)
  add_parts!(g, :H, 2; vertex=[src,tgt], inv=[k+2,k+1], kw...)
end

function add_half_edge_pairs!(g::AbstractHalfEdgeGraph, srcs::AbstractVector{Int},
                              tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :H)
  add_parts!(g, :H, 2n; vertex=vcat(srcs,tgts),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

""" Add a dangling edge to a half-edge graph.

A "dangling edge" is a half-edge that is paired with itself under the half-edge
involution. They are usually interpreted differently than "self-loops", i.e., a
pair of distinct half-edges incident to the same vertex.
"""
add_dangling_edge!(g::AbstractHalfEdgeGraph, v::Int; kw...) =
  add_part!(g, :H; vertex=v, inv=nparts(g,:H)+1)

""" Add multiple dangling edges to a half-edge graph.
"""
function add_dangling_edges!(g::AbstractHalfEdgeGraph, vs::AbstractVector{Int}; kw...)
  n, k = length(vs), nparts(g, :H)
  add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n), kw...)
end

function rem_vertices!(g::AbstractHalfEdgeGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    hs = flatten(incident(g, vs, :vertex))
    rem_parts!(g, :H, unique!(sort!([hs; inv(g, hs)])))
  end
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int) =
  rem_parts!(g, :H, sort!(unique(first.(half_edge_pairs(g, src, tgt)))))

rem_edge!(g::AbstractHalfEdgeGraph, h::Int) = rem_edges!(g, h:h)
rem_edges!(g::AbstractHalfEdgeGraph, hs) =
  rem_parts!(g, :H, unique!(sort!([hs; inv(g, hs)])))

# Weighted graphs
#################

@present TheoryWeightedGraph <: TheoryGraph begin
  Weight::AttrType
  weight::Attr(E,Weight)
end

""" Abstract type for weighted graphs.
"""
@abstract_acset_type AbstractWeightedGraph <: AbstractGraph

""" A weighted graph.

A graph in which every edge has a numerical weight.
"""
@acset_type WeightedGraph(TheoryWeightedGraph, index=[:src,:tgt]) <: AbstractWeightedGraph

""" Weight(s) of edge(s) in a weighted graph.
"""
weight(g::HasGraph, args...) = subpart(g, args..., :weight)

@present TheorySymmetricWeightedGraph <: TheorySymmetricGraph begin
  Weight::AttrType
  weight::Attr(E,Weight)

  compose(inv, weight) == weight
end

""" Abstract type for symmetric weighted graphs.
"""
@abstract_acset_type AbstractSymmetricWeightedGraph <: AbstractSymmetricGraph

""" A symmetric weighted graph.

A symmetric graph in which every edge has a numerical weight, preserved by the
edge involution.
"""
@acset_type SymmetricWeightedGraph(TheorySymmetricWeightedGraph, index=[:src]) <:
  AbstractSymmetricWeightedGraph

# JuliaGraphs constructors
##########################

function __init__()
  @require LightGraphs="093fc24a-ae57-5d10-9952-331d41423f4d" begin
    import .LightGraphs
    import .LightGraphs: SimpleGraph, SimpleDiGraph

    function (::Type{LG})(g::HasGraph) where LG <: Union{SimpleGraph,SimpleDiGraph}
      lg = LG(nv(g))
      for (s, t) in zip(src(g), tgt(g))
        LightGraphs.add_edge!(lg, s, t)
      end
      lg
    end

    function from_lightgraph(lg::SimpleDiGraph)
      g = Graph(LightGraphs.nv(lg))
      for e in LightGraphs.edges(lg)
        add_edge!(g,LightGraphs.src(e),LightGraphs.dst(e))
      end
      g
    end

    function from_lightgraph(lg::SimpleGraph)
      g = SymmetricGraph(LightGraphs.nv(lg))
      for e in LightGraphs.edges(lg)
        add_edge!(g,LightGraphs.src(e),LightGraphs.dst(e))
      end
      g
    end


    function SimpleGraph(g::AbstractHalfEdgeGraph)
      lg = SimpleGraph(nv(g))
      for e in half_edges(g)
        e′ = inv(g,e)
        if e <= e′
          LightGraphs.add_edge!(lg, vertex(g,e), vertex(g,e′))
        end
      end
      lg
    end
  end

  @require MetaGraphs="626554b9-1ddb-594c-aa3c-2596fe9399a5" begin
    import .MetaGraphs
    import .MetaGraphs: MetaGraph, MetaDiGraph

    MetaDiGraph(g::AbstractWeightedGraph{S, Tuple{U}}) where {S,U} =
      to_weighted_metagraph(MetaDiGraph{Int,U}, g)
    MetaGraph(g::AbstractSymmetricWeightedGraph{S, Tuple{U}}) where {S,U} =
      to_weighted_metagraph(MetaGraph{Int,U}, g)

    function to_weighted_metagraph(MG::Type{<:MetaGraphs.AbstractMetaGraph}, g)
      mg = MG(nv(g))
      for (s, t, w) in zip(src(g), tgt(g), weight(g))
        MetaGraphs.add_edge!(mg, s, t, :weight, w)
      end
      mg
    end
  end
end

end
