""" Embedded graphs, represented as C-sets.

The term *embedded graph* is used as in topological graph theory, graph drawing,
and related fields to mean a combinatorial structure representing a graph
embedded in an (oriented) surface, up to equivalence under
(orientation-preserving) homeomorphism.
"""
module EmbeddedGraphs
export σ, α, ϕ, trace_vertices, trace_edges, trace_faces,
  AbstractRotationGraph, RotationGraph, add_corolla!, pair_half_edges!,
  AbstractRotationSystem, RotationSystem,
  AbstractCombinatorialMap, CombinatorialMap

using ...Present, ...CSetDataStructures, ..BasicGraphs
using ...Permutations: cycles
using ..BasicGraphs: TheoryGraph, TheoryHalfEdgeGraph

# General properties
####################

""" Vertex permutation of rotation system or similar structure.
"""
σ(x::AbstractACSet, args...) = subpart(x, args..., :σ)

""" Edge permutation of rotation system or similar structure.
"""
α(x::AbstractACSet, args...) = subpart(x, args..., :α)

""" Face permutation of rotation system or similar structure.
"""
ϕ(x::AbstractACSet, args...) = subpart(x, args..., :ϕ)

""" Trace vertices of rotation system or similar, returning a list of cycles.
"""
trace_vertices(x::AbstractACSet) = cycles(σ(x))

""" Trace edges of rotation system or similar, return a listing of cycles.

Usually the cycles will be pairs of half edges but in a hypermap the cycles can
be arbitrary.
"""
trace_edges(x::AbstractACSet) = cycles(α(x))

""" Trace faces of rotation system or similar, returning list of cycles.
"""
trace_faces(x::AbstractACSet) = cycles(ϕ(x))

# Rotation graphs
#################

@present TheoryRotationGraph <: TheoryHalfEdgeGraph begin
  σ::Hom(H,H)

  compose(σ, vertex) == vertex
end

const AbstractRotationGraph = AbstractACSetType(TheoryRotationGraph)
const RotationGraph = CSetType(TheoryRotationGraph, index=[:vertex])

α(g::AbstractRotationGraph) = inv(g)
ϕ(g::AbstractRotationGraph) = sortperm(inv(g)[σ(g)]) # == (σ ⋅ inv)⁻¹

""" Add corolla to rotation graph, rotation system, or similar structure.

A *corolla* is a vertex together with its incident half-edges, the number of
which is its *valence*. The rotation on the half-edges is the consecutive one
induced by the half-edge part numbers.
"""
function add_corolla!(g::AbstractRotationGraph, valence::Int; kw...)
  v = add_vertex!(g; kw...)
  n = nparts(g, :H)
  add_parts!(g, :H, valence; vertex=v, σ=circshift((n+1):(n+valence), -1))
end

""" Pair together half-edges into edges.
"""
pair_half_edges!(g::AbstractRotationGraph, h, h′) =
  set_subpart!(g, [h; h′], :inv, [h′; h])

# Rotation systems
##################

@present TheoryRotationSystem(FreeSchema) begin
  H::Ob
  σ::Hom(H,H)
  α::Hom(H,H)

  compose(α, α) == id(H)
end

const AbstractRotationSystem = AbstractACSetType(TheoryRotationSystem)
const RotationSystem = CSetType(TheoryRotationSystem)

# ϕ == (σ⋅α)⁻¹ == α⁻¹ ⋅ σ⁻¹
ϕ(sys::AbstractRotationSystem) = sortperm(α(sys)[σ(sys)])

function add_corolla!(sys::AbstractRotationSystem, valence::Int)
  n = nparts(sys, :H)
  add_parts!(sys, :H, valence; σ=circshift((n+1):(n+valence), -1))
end

pair_half_edges!(sys::AbstractRotationSystem, h, h′) =
  set_subpart!(sys, [h; h′], :α, [h′; h])

# Combinatorial maps
####################

@present TheoryHypermap(FreeSchema) begin
  H::Ob
  σ::Hom(H,H)
  α::Hom(H,H)
  ϕ::Hom(H,H)

  compose(σ, α, ϕ) == id(H)
end

@present TheoryCombinatorialMap <: TheoryHypermap begin
  compose(α, α) == id(H)
end

const AbstractCombinatorialMap = AbstractACSetType(TheoryCombinatorialMap)
const CombinatorialMap = CSetType(TheoryCombinatorialMap)

# TODO: What kind of interface should we have for maps and hypermaps?

# Commutative graphs
####################

@present TheoryEmbeddedCommutativeGraph(FreeSchema) begin
  V::Ob # vertices
  L::Ob # left edges
  R::Ob # right edges
  F::Ob # faces

  # Source and target vertices of edges and faces.
  srcL::Hom(L,V)
  tgtL::Hom(L,V)
  srcR::Hom(R,V)
  tgtR::Hom(R,V)
  srcF::Hom(F,V)
  tgtF::Hom(F,V)

  # Left and right directed paths.
  ϕL::Hom(L,L)
  ϕR::Hom(R,R)
  compose(ϕL, srcL) == tgtL
  compose(ϕR, srcR) == tgtR

  # Start loops for left and right paths.
  startL::Hom(F,L)
  startR::Hom(F,R)
  compose(startL, srcL) == srcF
  compose(startL, tgtL) == srcF
  compose(startR, srcR) == srcF
  compose(startR, tgtR) == srcF

  # Stop loops for left and right paths.
  stopL::Hom(F,L)
  stopR::Hom(F,R)
  compose(stopL, srcL) == tgtF
  compose(stopL, tgtL) == tgtF
  compose(stopR, srcR) == tgtF
  compose(stopR, tgtR) == tgtF
  compose(stopL, ϕL) == stopL
  compose(stopR, ϕR) == stopR
end

end
