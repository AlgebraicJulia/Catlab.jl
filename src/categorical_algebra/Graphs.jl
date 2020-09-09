""" Data structures for graphs, based on C-sets.

Support for graphs, symmetric graphs, and property graphs.
"""
module Graphs
export AbstractGraph, Graph, AbstractSymmetricGraph, SymmetricGraph,
  nv, ne, src, tgt, inv, edges, vertices, has_edge, has_vertex,
  add_edge!, add_edges!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors,
  AbstractHalfEdgeGraph, HalfEdgeGraph, vertex, half_edges,
  add_dangling_edge!, add_dangling_edges!,
  AbstractPropertyGraph, PropertyGraph, SymmetricPropertyGraph,
  gprops, vprops, eprops, get_gprop, get_vprop, get_eprop,
  set_gprop!, set_vprop!, set_eprop!, set_gprops!, set_vprops!, set_eprops!

import Base: inv
using Compat: isnothing
import LightGraphs: SimpleGraph, SimpleDiGraph, nv, ne, src, dst,
  edges, vertices, has_edge, has_vertex, add_edge!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

using ...Present
using ...Theories: SchemaType
using ..CSets

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

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

# # Symmetric graphs
# ##################

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

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

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

add_edge!(g::AbstractHalfEdgeGraph, src::Int, tgt::Int; kw...) =
  add_edges!(g, src:src, tgt:tgt; kw...)

function add_edges!(g::AbstractHalfEdgeGraph, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}; kw...)
  @assert (n = length(srcs)) == length(tgts)
  k = nparts(g, :H)
  add_parts!(g, :H, 2n; vertex=vcat(srcs,tgts),
             inv=vcat((k+n+1):(k+2n),(k+1):(k+n)), kw...)
end

add_dangling_edge!(g::AbstractHalfEdgeGraph, v::Int; kw...) =
  add_part!(g, :H; vertex=v, inv=nparts(g,:H)+1)

function add_dangling_edges!(g::AbstractHalfEdgeGraph,
                             vs::AbstractVector{Int}; kw...)
  n, k = length(vs), nparts(g, :H)
  add_parts!(g, :H, n; vertex=vs, inv=(k+1):(k+n), kw...)
end

# Property graphs
#################

""" Abstract type for graph with properties.

Concrete types are [`PropertyGraph`](@ref) and [`SymmetricPropertyGraph`](@ref).
"""
abstract type AbstractPropertyGraph{T} end

@present TheoryPropertyGraph <: TheoryGraph begin
  Props::Data
  vprops::Attr(V,Props)
  eprops::Attr(E,Props)
end

# We don't use `ACSetType` because we are being a bit more flexible here.
const _AbstractPropertyGraph{T} = AbstractACSet{
  SchemaType(TheoryPropertyGraph)...,Tuple{Dict{Symbol,T}}}
const _PropertyGraph{T} = ACSet{
  SchemaType(TheoryPropertyGraph)...,Tuple{Dict{Symbol,T}},(:src,:tgt),()}

""" Graph with properties.

"Property graphs" are graphs with arbitrary named properties on the graph,
vertices, and edges. They are intended for applications with a large number of
ad-hoc properties. If you have a small number of known properties, it is better
and more efficient to create a specialized C-set type using [`CSetType`](@ref).

See also: [`SymmetricPropertyGraph`](@ref).
"""
struct PropertyGraph{T,G<:_AbstractPropertyGraph{T}} <: AbstractPropertyGraph{T}
  graph::G
  gprops::Dict{Symbol,T}
end

PropertyGraph{T,G}(; kw...) where {T,G<:_AbstractPropertyGraph{T}} =
  PropertyGraph(G(), Dict{Symbol,T}(kw...))
PropertyGraph{T}(; kw...) where T = PropertyGraph{T,_PropertyGraph{T}}(; kw...)

@present TheorySymmetricPropertyGraph <: TheorySymmetricGraph begin
  Props::Data
  vprops::Attr(V,Props)
  eprops::Attr(E,Props)

  compose(inv,eprops) == eprops # Edge involution preserves edge properties.
end

const _AbstractSymmetricPropertyGraph{T} = AbstractACSet{
  SchemaType(TheorySymmetricPropertyGraph)...,Tuple{Dict{Symbol,T}}}
const _SymmetricPropertyGraph{T} = ACSet{
  SchemaType(TheorySymmetricPropertyGraph)...,Tuple{Dict{Symbol,T}},(:src,),()}

""" Symmetric graphs with properties.

The edge properties are preserved under the edge involution, so these can be
interpreted as "undirected" property (multi)graphs.

See also: [`PropertyGraph`](@ref).
"""
struct SymmetricPropertyGraph{T,G<:_AbstractSymmetricPropertyGraph{T}} <:
    AbstractPropertyGraph{T}
  graph::G
  gprops::Dict{Symbol,T}
end

SymmetricPropertyGraph{T,G}(; kw...) where {T,G<:_AbstractSymmetricPropertyGraph{T}} =
  SymmetricPropertyGraph(G(),
                         Dict{Symbol,T}(kw...))
SymmetricPropertyGraph{T}(; kw...) where T =
  SymmetricPropertyGraph{T,_SymmetricPropertyGraph{T}}(; kw...)

gprops(g::AbstractPropertyGraph) = g.gprops
vprops(g::AbstractPropertyGraph, v) = subpart(g.graph, v, :vprops)
eprops(g::AbstractPropertyGraph, e) = subpart(g.graph, e, :eprops)

get_gprop(g::AbstractPropertyGraph, key::Symbol) = gprops(g)[key]
get_vprop(g::AbstractPropertyGraph, v, key::Symbol) =
  broadcast(v) do v; vprops(g,v)[key] end
get_eprop(g::AbstractPropertyGraph, e, key::Symbol) =
  broadcast(e) do e; eprops(g,e)[key] end

set_gprop!(g::AbstractPropertyGraph, key::Symbol, value) =
  (gprops(g)[key] = value)
set_vprop!(g::AbstractPropertyGraph, v, key::Symbol, value) =
  broadcast(v, value) do v, value; vprops(g,v)[key] = value end
set_eprop!(g::AbstractPropertyGraph, e, key::Symbol, value) =
  broadcast(e, value) do e, value; eprops(g,e)[key] = value end

set_gprops!(g::AbstractPropertyGraph; kw...) = merge!(gprops(g), kw)
set_vprops!(g::AbstractPropertyGraph, v::Int; kw...) = merge!(vprops(g,v), kw)
set_eprops!(g::AbstractPropertyGraph, e::Int; kw...) = merge!(eprops(g,e), kw)
set_gprops!(g::AbstractPropertyGraph, d::AbstractDict) = merge!(gprops(g), d)
set_vprops!(g::AbstractPropertyGraph, v::Int, d::AbstractDict) =
  merge!(vprops(g,v), d)
set_eprops!(g::AbstractPropertyGraph, e::Int, d::AbstractDict) =
  merge!(eprops(g,e), d)

@inline nv(g::AbstractPropertyGraph) = nv(g.graph)
@inline ne(g::AbstractPropertyGraph) = ne(g.graph)
@inline src(g::AbstractPropertyGraph, args...) = src(g.graph, args...)
@inline tgt(g::AbstractPropertyGraph, args...) = tgt(g.graph, args...)
@inline dst(g::AbstractPropertyGraph, args...) = dst(g.graph, args...)
@inline inv(g::SymmetricPropertyGraph, args...) = inv(g.graph, args...)
@inline vertices(g::AbstractPropertyGraph) = vertices(g.graph)
@inline edges(g::AbstractPropertyGraph) = edges(g.graph)
@inline has_vertex(g::AbstractPropertyGraph, v::Int) = has_vertex(g.graph, v)
@inline has_edge(g::AbstractPropertyGraph, e::Int) = has_edge(g.graph, e)

add_vertex!(g::AbstractPropertyGraph{T}; kw...) where T =
  add_vertex!(g, Dict{Symbol,T}(kw...))
add_vertex!(g::AbstractPropertyGraph{T}, d::Dict{Symbol,T}) where T =
  add_part!(g.graph, :V, vprops=d)

add_vertices!(g::AbstractPropertyGraph{T}, n::Int) where T =
  add_parts!(g.graph, :V, n, vprops=[Dict{Symbol,T}() for i=1:n])

add_edge!(g::AbstractPropertyGraph{T}, src::Int, tgt::Int; kw...) where T =
  add_edge!(g, src, tgt, Dict{Symbol,T}(kw...))

# Non-symmetric case.

add_edge!(g::PropertyGraph{T}, src::Int, tgt::Int, d::Dict{Symbol,T}) where T =
  add_part!(g.graph, :E, src=src, tgt=tgt, eprops=d)

function add_edges!(g::PropertyGraph{T}, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}, eprops=nothing) where T
  @assert (n = length(srcs)) == length(tgts)
  if isnothing(eprops)
    eprops = [Dict{Symbol,T}() for i=1:n]
  end
  add_parts!(g.graph, :E, n, src=srcs, tgt=tgts, eprops=eprops)
end

# Symmetric case.

add_edge!(g::SymmetricPropertyGraph{T}, src::Int, tgt::Int,
          d::Dict{Symbol,T}) where T =
 add_edges!(g, src:src, tgt:tgt, [d])

function add_edges!(g::SymmetricPropertyGraph{T}, srcs::AbstractVector{Int},
                    tgts::AbstractVector{Int}, eprops=nothing) where T
  @assert (n = length(srcs)) == length(tgts)
  if isnothing(eprops)
    eprops = [ Dict{Symbol,T}() for i=1:n ]
  end
  invs = nparts(g.graph, :E) .+ [(n+1):2n; 1:n]
  eprops = [eprops; eprops] # Share dictionaries to ensure equal properties.
  add_parts!(g.graph, :E, 2n, src=[srcs; tgts], tgt=[tgts; srcs],
             inv=invs, eprops=eprops)
end

# Constructors from graphs
#-------------------------

function PropertyGraph{T}(g::Graph, make_vprops, make_eprops; gprops...) where T
  pg = PropertyGraph{T}(; gprops...)
  add_vertices!(pg, nv(g))
  add_edges!(pg, src(g), tgt(g))
  for v in vertices(g)
    set_vprops!(pg, v, make_vprops(v))
  end
  for e in edges(g)
    set_eprops!(pg, e, make_eprops(e))
  end
  pg
end

PropertyGraph{T}(g::Graph; gprops...) where T =
  PropertyGraph{T}(g, v->Dict(), e->Dict(); gprops...)

function SymmetricPropertyGraph{T}(g::SymmetricGraph,
                                   make_vprops, make_eprops; gprops...) where T
  pg = SymmetricPropertyGraph{T}(; gprops...)
  add_vertices!(pg, nv(g))
  for v in vertices(g)
    set_vprops!(pg, v, make_vprops(v))
  end
  for e in edges(g)
    if e <= inv(g,e)
      e1, e2 = add_edge!(pg, src(g,e), tgt(g,e))
      set_eprops!(pg, e1, make_eprops(e))
    end
  end
  pg
end

SymmetricPropertyGraph{T}(g::SymmetricGraph; gprops...) where T =
  SymmetricPropertyGraph{T}(g, v->Dict(), e->Dict(); gprops...)

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
