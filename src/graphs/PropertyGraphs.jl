module PropertyGraphs
export AbstractPropertyGraph, PropertyGraph, SchPropertyGraph,
  SymmetricPropertyGraph, SchSymmetricPropertyGraph,
  ReflexiveEdgePropertyGraph, SchReflexivePropertyGraph,
  gprops, vprops, eprops, get_gprop, get_vprop, get_eprop,
  set_gprop!, set_vprop!, set_eprop!, set_gprops!, set_vprops!, set_eprops!,
  AbstractBipartitePropertyGraph, BipartitePropertyGraph, SchBipartitePropertyGraph,
  v₁props, v₂props, e₁₂props, e₂₁props, get_v₁prop, get_v₂prop,
  get_e₁₂prop, get_e₂₁prop, set_v₁prop!, set_v₂prop!, set_e₁₂prop!, set_e₂₁prop!,
  set_v₁props!, set_v₂props!, set_e₁₂props!, set_e₂₁props!

using ACSets
using ...Theories
using ..BasicGraphs
import ..BasicGraphs: nv, ne, src, tgt, inv, edges, vertices,
  has_edge, has_vertex, add_edge!, add_edges!, add_vertex!, add_vertices!
using ..BipartiteGraphs
import ..BipartiteGraphs: nv₁, nv₂, vertices₁, vertices₂, ne₁₂, ne₂₁, edges₁₂, edges₂₁,
  src₁, src₂, tgt₁, tgt₂,
  add_vertex₁!, add_vertex₂!, add_vertices₁!, add_vertices₂!,
  rem_vertex₁!, rem_vertex₂!, rem_vertices₁!, rem_vertices₂!,
  add_edge₁₂!, add_edge₂₁!, add_edges₁₂!, add_edges₂₁!,
  rem_edge₁₂!, rem_edge₂₁!, rem_edges₁₂!, rem_edges₂₁!

# Data types
############

""" Abstract type for graph with properties.

Concrete types are [`PropertyGraph`](@ref) and [`SymmetricPropertyGraph`](@ref).
"""
abstract type AbstractPropertyGraph{T} end

@present SchPropertyGraph <: SchGraph begin
  Props::AttrType
  vprops::Attr(V,Props)
  eprops::Attr(E,Props)
end

@abstract_acset_type __AbstractPropertyGraph <: HasGraph

const _AbstractPropertyGraph{T} = __AbstractPropertyGraph{S, Tuple{Dict{Symbol,T}}} where {S}

@acset_type __PropertyGraph(SchPropertyGraph, index=[:src,:tgt]) <: __AbstractPropertyGraph

const _PropertyGraph{T} = __PropertyGraph{Dict{Symbol,T}}

""" Graph with properties.

"Property graphs" are graphs with arbitrary named properties on the graph,
vertices, and edges. They are intended for applications with a large number of
ad-hoc properties. If you have a small number of known properties, it is better
and more efficient to create a specialized C-set type using `@acset_type`.

See also: [`SymmetricPropertyGraph`](@ref).
"""
struct PropertyGraph{T,G<:_AbstractPropertyGraph{T}} <: AbstractPropertyGraph{T}
  graph::G
  gprops::Dict{Symbol,T}
end

PropertyGraph{T,G}(; kw...) where {T,G<:_AbstractPropertyGraph{T}} =
  PropertyGraph(G(), Dict{Symbol,T}(kw...))
PropertyGraph{T}(; kw...) where T = PropertyGraph{T,_PropertyGraph{T}}(; kw...)

@present SchSymmetricPropertyGraph <: SchSymmetricGraph begin
  Props::AttrType
  vprops::Attr(V,Props)
  eprops::Attr(E,Props)

  compose(inv,eprops) == eprops # Edge involution preserves edge properties.
end

@abstract_acset_type __AbstractSymmetricPropertyGraph <: HasGraph

const _AbstractSymmetricPropertyGraph{T} = __AbstractSymmetricPropertyGraph{S, Tuple{Dict{Symbol,T}}} where {S}

@acset_type __SymmetricPropertyGraph(SchSymmetricPropertyGraph, index=[:src,:tgt]) <:
  __AbstractSymmetricPropertyGraph

const _SymmetricPropertyGraph{T} = __SymmetricPropertyGraph{Dict{Symbol,T}}

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
  SymmetricPropertyGraph(G(), Dict{Symbol,T}(kw...))
SymmetricPropertyGraph{T}(; kw...) where T =
  SymmetricPropertyGraph{T,_SymmetricPropertyGraph{T}}(; kw...)


@present SchReflexiveEdgePropertyGraph <: SchReflexiveGraph begin
  Props::AttrType
  eprops::Attr(E,Props)
end

@abstract_acset_type AbstractReflexiveEdgePropertyGraph <: HasGraph
@acset_type ReflexiveEdgePropertyGraph(SchReflexiveEdgePropertyGraph, index=[:src,:tgt]) <:
  AbstractReflexiveEdgePropertyGraph

""" Abstract type for bipartite graph with properties.

Concrete types are [`BipartitePropertyGraph`](@ref).
"""
abstract type AbstractBipartitePropertyGraph{T} end

@present SchBipartitePropertyGraph <: SchBipartiteGraph begin
  Props::AttrType
  v₁props::Attr(V₁,Props)
  v₂props::Attr(V₂,Props)
  e₁₂props::Attr(E₁₂,Props)
  e₂₁props::Attr(E₂₁,Props)
end

@abstract_acset_type __AbstractBipartitePropertyGraph <: HasBipartiteGraph

const _AbstractBipartitePropertyGraph{T} = __AbstractBipartitePropertyGraph{S, Tuple{Dict{Symbol,T}}} where {S}

@acset_type __BipartitePropertyGraph(SchBipartitePropertyGraph, index=[:src₁, :src₂, :tgt₁, :tgt₂]) <: __AbstractBipartitePropertyGraph

const _BipartitePropertyGraph{T} = __BipartitePropertyGraph{Dict{Symbol,T}}

""" Bipartite graph with properties.

"Property graphs" are graphs with arbitrary named properties on the graph,
vertices, and edges. They are intended for applications with a large number of
ad-hoc properties. If you have a small number of known properties, it is better
and more efficient to create a specialized C-set type using `@acset_type`.
"""
struct BipartitePropertyGraph{T,G<:_AbstractBipartitePropertyGraph{T}} <: AbstractBipartitePropertyGraph{T}
  graph::G
  gprops::Dict{Symbol,T}
end

BipartitePropertyGraph{T,G}(; kw...) where {T,G<:_AbstractBipartitePropertyGraph{T}} = BipartitePropertyGraph(G(), Dict{Symbol,T}(kw...))
BipartitePropertyGraph{T}(; kw...) where T = BipartitePropertyGraph{T,_BipartitePropertyGraph{T}}(; kw...)

# Accessors and mutators
########################

""" Graph-level properties of a property graph.
"""
gprops(g::AbstractPropertyGraph) = g.gprops

""" Properties of vertex in a property graph.
"""
vprops(g::AbstractPropertyGraph, v) = subpart(g.graph, v, :vprops)

""" Properties of edge in a property graph.
"""
eprops(g::AbstractPropertyGraph, e) = subpart(g.graph, e, :eprops)

""" Get graph-level property of a property graph.
"""
get_gprop(g::AbstractPropertyGraph, key::Symbol) = gprops(g)[key]

""" Get property of vertex or vertices in a property graph.
"""
get_vprop(g::AbstractPropertyGraph, v, key::Symbol) =
  broadcast(v) do v; vprops(g,v)[key] end

""" Get property of edge or edges in a property graph.
"""
get_eprop(g::AbstractPropertyGraph, e, key::Symbol) =
  broadcast(e) do e; eprops(g,e)[key] end

""" Set graph-level property in a property graph.
"""
set_gprop!(g::AbstractPropertyGraph, key::Symbol, value) =
  (gprops(g)[key] = value)

""" Set property of vertex or vertices in a property graph.
"""
set_vprop!(g::AbstractPropertyGraph, v, key::Symbol, value) =
  broadcast(v, value) do v, value; vprops(g,v)[key] = value end

""" Set property of edge or edges in a property graph.
"""
set_eprop!(g::AbstractPropertyGraph, e, key::Symbol, value) =
  broadcast(e, value) do e, value; eprops(g,e)[key] = value end

""" Set multiple graph-level properties in a property graph.
"""
set_gprops!(g::AbstractPropertyGraph; kw...) = merge!(gprops(g), kw)
set_gprops!(g::AbstractPropertyGraph, d::AbstractDict) = merge!(gprops(g), d)

""" Set multiple properties of a vertex in a property graph.
"""
set_vprops!(g::AbstractPropertyGraph, v::Int; kw...) = merge!(vprops(g,v), kw)
set_vprops!(g::AbstractPropertyGraph, v::Int, d::AbstractDict) =
  merge!(vprops(g,v), d)

""" Set multiple properties of an edge in a property graph.
"""
set_eprops!(g::AbstractPropertyGraph, e::Int; kw...) = merge!(eprops(g,e), kw)
set_eprops!(g::AbstractPropertyGraph, e::Int, d::AbstractDict) =
  merge!(eprops(g,e), d)

@inline nv(g::AbstractPropertyGraph) = nv(g.graph)
@inline ne(g::AbstractPropertyGraph) = ne(g.graph)
@inline src(g::AbstractPropertyGraph, args...) = src(g.graph, args...)
@inline tgt(g::AbstractPropertyGraph, args...) = tgt(g.graph, args...)
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

# Bipartite property graphs

# interface from BipartiteGraphs
@inline nv₁(g::AbstractBipartitePropertyGraph) = nv₁(g.graph)
@inline nv₂(g::AbstractBipartitePropertyGraph) = nv₂(g.graph)
@inline vertices₁(g::AbstractBipartitePropertyGraph) = vertices₁(g.graph)
@inline vertices₂(g::AbstractBipartitePropertyGraph) = vertices₂(g.graph)
@inline ne₁₂(g::AbstractBipartitePropertyGraph) = ne₁₂(g.graph)
@inline ne₁₂(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = ne₁₂(g.graph, src, tgt)
@inline ne₂₁(g::AbstractBipartitePropertyGraph) = ne₂₁(g.graph)
@inline ne₂₁(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = ne₂₁(g.graph, src, tgt)
@inline edges₁₂(g::AbstractBipartitePropertyGraph) = edges₁₂(g.graph)
@inline edges₁₂(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = edges₁₂(g.graph, src, tgt)
@inline edges₂₁(g::AbstractBipartitePropertyGraph) = edges₂₁(g.graph)
@inline edges₂₁(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = edges₂₁(g.graph, src, tgt)
@inline src₁(g::AbstractBipartitePropertyGraph, args...) = src₁(g.graph, args...)
@inline tgt₂(g::AbstractBipartitePropertyGraph, args...) = tgt₂(g.graph, args...)
@inline src₂(g::AbstractBipartitePropertyGraph, args...) = src₂(g.graph, args...)
@inline tgt₁(g::AbstractBipartitePropertyGraph, args...) = tgt₁(g.graph, args...)
@inline rem_vertex₁!(g::AbstractBipartitePropertyGraph, v::Int; kw...) = rem_vertex₁!(g.graph, v; kw...)
@inline rem_vertex₂!(g::AbstractBipartitePropertyGraph, v::Int; kw...) = rem_vertex₂!(g.graph, v; kw...)
@inline rem_vertices₁!(g::AbstractBipartitePropertyGraph, vs; keep_edges::Bool=false) = rem_vertices₁!(g.graph, vs; keep_edges)
@inline rem_vertices₂!(g::AbstractBipartitePropertyGraph, vs; keep_edges::Bool=false) = rem_vertices₂!(g.graph, vs; keep_edges)
@inline rem_edge₁₂!(g::AbstractBipartitePropertyGraph, e::Int) = rem_edge₁₂!(g.graph, e)
@inline rem_edge₁₂!(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = rem_edge₁₂!(g.graph, src, tgt)
@inline rem_edge₂₁!(g::AbstractBipartitePropertyGraph, e::Int) = rem_edge₂₁!(g.graph, e)
@inline rem_edge₂₁!(g::AbstractBipartitePropertyGraph, src::Int, tgt::Int) = rem_edge₂₁!(g.graph, src, tgt)
@inline rem_edges₁₂!(g::AbstractBipartitePropertyGraph, es) = rem_edges₁₂!(g.graph, es)
@inline rem_edges₂₁!(g::AbstractBipartitePropertyGraph, es) = rem_edges₂₁!(g.graph, es)

# interface from BasicGraphs
@inline nv(g::AbstractBipartitePropertyGraph) = nv(g.graph)
@inline vertices(g::AbstractBipartitePropertyGraph) = vertices(g.graph)
@inline ne(g::AbstractBipartitePropertyGraph) = ne(g.graph)
@inline edges(g::AbstractBipartitePropertyGraph) = edges(g.graph)

add_vertex₁!(g::AbstractBipartitePropertyGraph{T}; kw...) where T =
  add_vertex₁!(g, Dict{Symbol,T}(kw...))
add_vertex₁!(g::AbstractBipartitePropertyGraph{T}, d::Dict{Symbol,T}) where T =
  add_vertex₁!(g.graph, v₁props=d)

add_vertex₂!(g::AbstractBipartitePropertyGraph{T}; kw...) where T =
  add_vertex₂!(g, Dict{Symbol,T}(kw...))
add_vertex₂!(g::AbstractBipartitePropertyGraph{T}, d::Dict{Symbol,T}) where T =
  add_vertex₂!(g.graph, v₂props=d)

add_vertices₁!(g::AbstractBipartitePropertyGraph{T}, n::Int; kw...) where T =
  add_vertices₁!(g.graph, n, v₁props=[Dict{Symbol,T}(kw...) for _=1:n])
add_vertices₂!(g::AbstractBipartitePropertyGraph{T}, n::Int; kw...) where T =
  add_vertices₂!(g.graph, n, v₂props=[Dict{Symbol,T}(kw...) for _=1:n])

add_edge₁₂!(g::AbstractBipartitePropertyGraph{T}, src::Int, tgt::Int; kw...) where T =
  add_edge₁₂!(g.graph, src, tgt, e₁₂props=Dict{Symbol,T}(kw...))
add_edge₂₁!(g::AbstractBipartitePropertyGraph{T}, src::Int, tgt::Int; kw...) where T =
  add_edge₂₁!(g.graph, src, tgt, e₂₁props=Dict{Symbol,T}(kw...))

add_edges₁₂!(g::AbstractBipartitePropertyGraph{T}, srcs::AbstractVector{Int},
            tgts::AbstractVector{Int}; kw...) where T =
  add_edges₁₂!(g.graph, srcs, tgts, e₁₂props=[Dict{Symbol,T}(kw...) for _=1:length(srcs)])

add_edges₂₁!(g::AbstractBipartitePropertyGraph{T}, srcs::AbstractVector{Int},
            tgts::AbstractVector{Int}; kw...) where T =
  add_edges₂₁!(g.graph, srcs, tgts, e₂₁props=[Dict{Symbol,T}(kw...) for _=1:length(srcs)])

# Property graph interface

""" Graph-level properties of a bipartite property graph.
"""
gprops(g::AbstractBipartitePropertyGraph) = g.gprops

""" Get graph-level property of a bipartite property graph.
"""
get_gprop(g::AbstractBipartitePropertyGraph, key::Symbol) = gprops(g)[key]

""" Set graph-level property in a bipartite property graph.
"""
set_gprop!(g::AbstractBipartitePropertyGraph, key::Symbol, value) =
  (gprops(g)[key] = value)

""" Set multiple graph-level properties in a property graph.
"""
set_gprops!(g::AbstractBipartitePropertyGraph; kw...) = merge!(gprops(g), kw)
set_gprops!(g::AbstractBipartitePropertyGraph, d::AbstractDict) = merge!(gprops(g), d)

""" Properties of vertex of type V₁ in a bipartite property graph.
"""
v₁props(g::AbstractBipartitePropertyGraph, v) = subpart(g.graph, v, :v₁props) 

""" Properties of vertex of type V₂ in a bipartite property graph.
"""
v₂props(g::AbstractBipartitePropertyGraph, v) = subpart(g.graph, v, :v₂props) 

""" Properties of edge from V₁ to V₂ in a bipartite property graph.
"""
e₁₂props(g::AbstractBipartitePropertyGraph, v) = subpart(g.graph, v, :e₁₂props) 

""" Properties of edge from V₂ to V₁ in a bipartite property graph.
"""
e₂₁props(g::AbstractBipartitePropertyGraph, v) = subpart(g.graph, v, :e₂₁props) 

""" Get property of vertex or vertices of type V₁ in a bipartite property graph.
"""
get_v₁prop(g::AbstractBipartitePropertyGraph, v, key::Symbol) =
  broadcast(v) do v; v₁props(g,v)[key] end

""" Get property of vertex or vertices of type V₂ in a bipartite property graph.
"""
get_v₂prop(g::AbstractBipartitePropertyGraph, v, key::Symbol) =
  broadcast(v) do v; v₂props(g,v)[key] end

""" Get property of edge or edges from V₁ to V₂ in a bipartite property graph.
"""
get_e₁₂prop(g::AbstractBipartitePropertyGraph, e, key::Symbol) =
  broadcast(e) do e; e₁₂props(g,e)[key] end

""" Get property of edge or edges from V₂ to V₁ in a bipartite property graph.
"""
get_e₂₁prop(g::AbstractBipartitePropertyGraph, e, key::Symbol) =
  broadcast(e) do e; e₂₁props(g,e)[key] end

""" Set property of vertex or vertices of type V₁ in a bipartite property graph.
"""
set_v₁prop!(g::AbstractBipartitePropertyGraph, v, key::Symbol, value) =
  broadcast(v, value) do v, value; v₁props(g,v)[key] = value end

""" Set property of vertex or vertices of type V₂ in a bipartite property graph.
"""
set_v₂prop!(g::AbstractBipartitePropertyGraph, v, key::Symbol, value) =
  broadcast(v, value) do v, value; v₂props(g,v)[key] = value end

""" Set property of edge or edges from V₁ to V₂ in a bipartite property graph.
"""
set_e₁₂prop!(g::AbstractBipartitePropertyGraph, e, key::Symbol, value) =
  broadcast(e, value) do e, value; e₁₂props(g,e)[key] = value end

""" Set property of edge or edges from V₂ to V₁ in a bipartite property graph.
"""
set_e₂₁prop!(g::AbstractBipartitePropertyGraph, e, key::Symbol, value) =
  broadcast(e, value) do e, value; e₂₁props(g,e)[key] = value end

""" Set multiple properties of a vertex of type V₁ in a bipartite property graph.
"""
set_v₁props!(g::AbstractBipartitePropertyGraph, v::Int; kw...) = merge!(v₁props(g,v), kw)
set_v₁props!(g::AbstractBipartitePropertyGraph, v::Int, d::AbstractDict) =
  merge!(v₁props(g,v), d)

""" Set multiple properties of a vertex of type V₂ in a bipartite property graph.
"""
set_v₂props!(g::AbstractBipartitePropertyGraph, v::Int; kw...) = merge!(v₂props(g,v), kw)
set_v₂props!(g::AbstractBipartitePropertyGraph, v::Int, d::AbstractDict) =
  merge!(v₂props(g,v), d)

""" Set multiple properties of an edge from V₁ to V₂ in a bipartite property graph.
"""
set_e₁₂props!(g::AbstractBipartitePropertyGraph, e::Int; kw...) = merge!(e₁₂props(g,e), kw)
set_e₁₂props!(g::AbstractBipartitePropertyGraph, e::Int, d::AbstractDict) =
  merge!(e₁₂props(g,e), d)

""" Set multiple properties of an edge from V₂ to V₁ in a bipartite property graph.
"""
set_e₂₁props!(g::AbstractBipartitePropertyGraph, e::Int; kw...) = merge!(e₂₁props(g,e), kw)
set_e₂₁props!(g::AbstractBipartitePropertyGraph, e::Int, d::AbstractDict) =
  merge!(e₂₁props(g,e), d)

# Constructors from graphs
##########################

function PropertyGraph{T}(g::HasGraph, make_vprops, make_eprops;
                          gprops...) where T
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

PropertyGraph{T}(g::HasGraph; gprops...) where T =
  PropertyGraph{T}(g, v->Dict(), e->Dict(); gprops...)

function SymmetricPropertyGraph{T}(g::HasGraph, make_vprops, make_eprops;
                                   gprops...) where T
  pg = SymmetricPropertyGraph{T}(; gprops...)
  add_vertices!(pg, nv(g))
  for v in vertices(g)
    set_vprops!(pg, v, make_vprops(v))
  end
  for e in edges(g)
    if !has_subpart(g, :inv) || e <= inv(g,e)
      e1, e2 = add_edge!(pg, src(g,e), tgt(g,e))
      set_eprops!(pg, e1, make_eprops(e))
    end
  end
  pg
end

SymmetricPropertyGraph{T}(g::HasGraph; gprops...) where T =
  SymmetricPropertyGraph{T}(g, v->Dict(), e->Dict(); gprops...)

function BipartitePropertyGraph{T}(g::HasBipartiteVertices, make_v₁props, make_v₂props, 
                                   make_e₁₂props; gprops...) where {T}
  pg = BipartitePropertyGraph{T}(; gprops...)
  add_vertices₁!(pg, nv₁(g))
  add_vertices₂!(pg, nv₂(g))
  add_edges₁₂!(pg, src(g), tgt(g))
  for v in vertices₁(g)
    set_v₁props!(pg, v, make_v₁props(v))
  end
  for v in vertices₂(g)
    set_v₂props!(pg, v, make_v₂props(v))
  end
  for e in edges(g)
    set_e₁₂props!(pg, e, make_e₁₂props(e))
  end
  pg
end

BipartitePropertyGraph{T}(g::HasBipartiteVertices; gprops...) where T =
  BipartitePropertyGraph{T}(g, v₁->Dict(), v₂->Dict(), e₁₂->Dict(); gprops...)

function BipartitePropertyGraph{T}(g::HasBipartiteGraph, make_v₁props, make_v₂props, 
                                   make_e₁₂props, make_e₂₁props; gprops...) where {T}
  pg = BipartitePropertyGraph{T}(; gprops...)
  add_vertices₁!(pg, nv₁(g))
  add_vertices₂!(pg, nv₂(g))
  add_edges₁₂!(pg, src₁(g), tgt₂(g))
  add_edges₂₁!(pg, src₂(g), tgt₁(g))
  for v in vertices₁(g)
    set_v₁props!(pg, v, make_v₁props(v))
  end
  for v in vertices₂(g)
    set_v₂props!(pg, v, make_v₂props(v))
  end
  for e in edges₁₂(g)
    set_e₁₂props!(pg, e, make_e₁₂props(e))
  end
  for e in edges₂₁(g)
    set_e₂₁props!(pg, e, make_e₂₁props(e))
  end
  pg
end

BipartitePropertyGraph{T}(g::HasBipartiteGraph; gprops...) where T =
  BipartitePropertyGraph{T}(g, v₁->Dict(), v₂->Dict(), e₁₂->Dict(), e₂₁->Dict(); gprops...)

end
