""" Data structures for graphs, based on C-sets.

Provides the category theorist's four basic kinds of graphs: (directed) graphs,
symmetric graphs, reflexive graphs, and symmetric reflexive graphs. Also defines
half-edge graphs.
"""
module BasicGraphs
export AbstractGraph, Graph, nv, ne, src, tgt, edges, vertices,
  has_edge, has_vertex, add_edge!, add_edges!, add_vertex!, add_vertices!,
  rem_edge!, rem_edges!, rem_vertex!, rem_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors,
  AbstractSymmetricGraph, SymmetricGraph, inv,
  AbstractReflexiveGraph, ReflexiveGraph, refl,
  AbstractSymmetricReflexiveGraph, SymmetricReflexiveGraph,
  AbstractHalfEdgeGraph, HalfEdgeGraph, vertex, half_edges,
  add_dangling_edge!, add_dangling_edges!

using Compat: only

import Base: inv
import LightGraphs: SimpleGraph, SimpleDiGraph,
  nv, ne, src, dst, edges, vertices, has_edge, has_vertex,
  add_edge!, add_vertex!, add_vertices!, rem_edge!, rem_vertex!, rem_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

using ...Present, ...CSetDataStructures

# Graphs
########

@present TheoryGraph(FreeSchema) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

const AbstractGraph = AbstractACSetType(TheoryGraph)
const Graph = CSetType(TheoryGraph, index=[:src,:tgt])

function (::Type{T})(nv::Int) where T <: AbstractGraph
  g = T(); add_vertices!(g, nv); g
end

nv(g::AbstractACSet) = nparts(g, :V)
ne(g::AbstractACSet) = nparts(g, :E)
ne(g::AbstractACSet, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

src(g::AbstractACSet, args...) = subpart(g, args..., :src)
tgt(g::AbstractACSet, args...) = subpart(g, args..., :tgt)
dst(g::AbstractACSet, args...) = tgt(g, args...) # LightGraphs compatibility

vertices(g::AbstractACSet) = 1:nv(g)
edges(g::AbstractACSet) = 1:ne(g)
edges(g::AbstractACSet, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractACSet, v) = has_part(g, :V, v)
has_edge(g::AbstractACSet, e) = has_part(g, :E, e)
has_edge(g::AbstractACSet, src::Int, tgt::Int) = tgt ∈ outneighbors(g, src)

add_vertex!(g::AbstractACSet; kw...) = add_part!(g, :V; kw...)
add_vertices!(g::AbstractACSet, n::Int; kw...) = add_parts!(g, :V, n; kw...)

add_edge!(g::AbstractGraph, src::Int, tgt::Int; kw...) =
  add_part!(g, :E; src=src, tgt=tgt, kw...)

function add_edges!(g::AbstractGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E, n; src=srcs, tgt=tgts, kw...)
end

rem_vertex!(g::AbstractACSet, v::Int; kw...) = rem_vertices!(g, v:v; kw...)

function rem_vertices!(g::AbstractGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    es = reduce(vcat, [incident(g, vs, :src); incident(g, vs, :tgt)])
    rem_parts!(g, :E, unique!(sort!(es)))
  end
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractGraph, e::Int) = rem_part!(g, :E, e)
rem_edge!(g::AbstractACSet, src::Int, tgt::Int) =
  rem_edge!(g, first(edges(g, src, tgt)))

rem_edges!(g::AbstractGraph, es) = rem_parts!(g, :E, es)

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

# Symmetric graphs
##################

@present TheorySymmetricGraph <: TheoryGraph begin
  inv::Hom(E,E)

  compose(inv,inv) == id(E)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

# Don't index `inv` because it is self-inverse and don't index `tgt`
# because `src` contains the same information due to symmetry of graph.
const AbstractSymmetricGraph = AbstractACSetType(TheorySymmetricGraph)
const SymmetricGraph = CSetType(TheorySymmetricGraph, index=[:src])

function (::Type{T})(nv::Int) where T <: AbstractSymmetricGraph
  g = T(); add_vertices!(g, nv); g
end

inv(g::AbstractACSet, args...) = subpart(g, args..., :inv)

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
    es = reduce(vcat, incident(g, vs, :src))
    rem_parts!(g, :E, unique!(sort!([es; inv(g, es)])))
  end
  # FIXME: Inefficient when deleting incident edges since `rem_parts!` still
  # searches for edges with given targets but `tgt` is not indexed.
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

const AbstractReflexiveGraph = AbstractACSetType(TheoryReflexiveGraph)
const ReflexiveGraph = CSetType(TheoryReflexiveGraph, index=[:src,:tgt])

function (::Type{T})(nv::Int) where T <: AbstractReflexiveGraph
  g = T(); add_vertices!(g, nv); g
end

refl(g::AbstractACSet, args...) = subpart(g, args..., :refl)

add_vertex!(g::AbstractReflexiveGraph; kw...) =
  only(add_vertices!(g, 1; kw...))

function add_vertices!(g::AbstractReflexiveGraph, n::Int; kw...)
  vs = add_parts!(g, :V, n; kw...)
  es = add_parts!(g, :E, n, src=vs, tgt=vs)
  set_subpart!(g, vs, :refl, es)
  vs
end

add_edge!(g::AbstractReflexiveGraph, src::Int, tgt::Int; kw...) =
  add_part!(g, :E; src=src, tgt=tgt, kw...)

function add_edges!(g::AbstractReflexiveGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  add_parts!(g, :E, n; src=srcs, tgt=tgts, kw...)
end

function rem_vertices!(g::AbstractReflexiveGraph, vs; keep_edges::Bool=false)
  es = if keep_edges
    sort(refl(g, vs))
  else
    unique!(sort!(reduce(vcat, [incident(g, vs, :src); incident(g, vs, :tgt)])))
  end
  rem_parts!(g, :E, es)
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractReflexiveGraph, e::Int) = rem_part!(g, :E, e)
rem_edges!(g::AbstractReflexiveGraph, es) = rem_parts!(g, :E, es)

# Symmetric reflexive graphs
############################

@present TheorySymmetricReflexiveGraph <: TheorySymmetricGraph begin
  refl::Hom(V,E)

  compose(refl, src) == id(V)
  compose(refl, tgt) == id(V)
  compose(refl, inv) == refl # Reflexive loop fixed by involution.
end

const AbstractSymmetricReflexiveGraph =
  AbstractACSetType(TheorySymmetricReflexiveGraph)
const SymmetricReflexiveGraph =
  CSetType(TheorySymmetricReflexiveGraph, index=[:src])

function (::Type{T})(nv::Int) where T <: AbstractSymmetricReflexiveGraph
  g = T(); add_vertices!(g, nv); g
end

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

# Half-edge graphs
##################

@present TheoryHalfEdgeGraph(FreeSchema) begin
  V::Ob
  H::Ob
  vertex::Hom(H,V)
  inv::Hom(H,H)

  compose(inv, inv) == id(H)
end

const AbstractHalfEdgeGraph = AbstractACSetType(TheoryHalfEdgeGraph)
const HalfEdgeGraph = CSetType(TheoryHalfEdgeGraph, index=[:vertex])

function (::Type{T})(nv::Int) where T <: AbstractHalfEdgeGraph
  g = T(); add_vertices!(g, nv); g
end

vertex(g::AbstractACSet, args...) = subpart(g, args..., :vertex)

half_edges(g::AbstractACSet) = 1:nparts(g, :H)
half_edges(g::AbstractACSet, v) = incident(g, v, :vertex)

function half_edge_pairs(g::AbstractACSet, src::Int, tgt::Int)
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

function add_half_edge_pair!(g::AbstractACSet, src::Int, tgt::Int; kw...)
  k = nparts(g, :H)
  add_parts!(g, :H, 2; vertex=[src,tgt], inv=[k+2,k+1], kw...)
end

function add_half_edge_pairs!(g::AbstractACSet, srcs::AbstractVector{Int},
                              tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :H)
  add_parts!(g, :H, 2n; vertex=vcat(srcs,tgts),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

add_dangling_edge!(g::AbstractACSet, v::Int; kw...) =
  add_part!(g, :H; vertex=v, inv=nparts(g,:H)+1)

function add_dangling_edges!(g::AbstractACSet, vs::AbstractVector{Int}; kw...)
  n, k = length(vs), nparts(g, :H)
  add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n), kw...)
end

function rem_vertices!(g::AbstractHalfEdgeGraph, vs; keep_edges::Bool=false)
  if !keep_edges
    hs = reduce(vcat, incident(g, vs, :vertex))
    rem_parts!(g, :H, unique!(sort!([hs; inv(g, hs)])))
  end
  rem_parts!(g, :V, vs)
end

rem_edge!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int) =
  rem_parts!(g, :H, sort!(unique(first.(half_edge_pairs(g, src, tgt)))))

rem_edge!(g::AbstractHalfEdgeGraph, h::Int) = rem_edges!(g, h:h)
rem_edges!(g::AbstractHalfEdgeGraph, hs) =
  rem_parts!(g, :H, unique!(sort!([hs; inv(g, hs)])))

# LightGraphs constructors
##########################

function (::Type{LG})(g::Union{AbstractGraph,AbstractSymmetricGraph}) where
    LG <: Union{SimpleGraph,SimpleDiGraph}
  lg = LG(nv(g))
  for e in edges(g)
    add_edge!(lg, src(g,e), tgt(g,e))
  end
  lg
end

function SimpleGraph(g::AbstractHalfEdgeGraph)
  lg = SimpleGraph(nv(g))
  for e in half_edges(g)
    e′ = inv(g,e)
    if e <= e′
      add_edge!(lg, vertex(g,e), vertex(g,e′))
    end
  end
  lg
end

end
