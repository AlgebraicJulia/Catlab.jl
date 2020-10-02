""" Embedded graphs, represented as C-sets.

The term *embedded graph* is used as in topological graph theory, graph drawing,
and related fields to mean a combinatorial structure representing a graph
embedded in an (oriented) surface, up to equivalence under
(orientation-preserving) homeomorphism.
"""
module EmbeddedGraphs
export AbstractRotationGraph, RotationGraph, σ, add_corolla!, pair_half_edges!,
  trace_faces

using ...Present, ...CSetDataStructures, ..BasicGraphs
using ...Permutations: cycles
using ..BasicGraphs: TheoryHalfEdgeGraph

# Rotation graphs
#################

@present TheoryRotationGraph <: TheoryHalfEdgeGraph begin
  σ::Hom(H,H)

  compose(σ, vertex) == vertex
end

const AbstractRotationGraph = AbstractACSetType(TheoryRotationGraph)
const RotationGraph = CSetType(TheoryRotationGraph, index=[:vertex])

σ(g::AbstractACSet, args...) = subpart(g, args..., :σ)

""" Add corolla to rotation graph.

A *corolla* is a vertex together with its incident half-edges, the number of
which is its *valence*. The rotation on the half-edges is the consecutive one
induced by the half-edge part numbers.
"""
function add_corolla!(g::AbstractRotationGraph, valence::Int; kw...)
  v = add_vertex!(g)
  n = nparts(g, :H)
  add_parts!(g, :H, valence; vertex=v, σ=circshift((n+1):(n+valence), -1))
  v
end

pair_half_edges!(g::AbstractRotationGraph, h::Int, h′::Int) =
  pair_half_edges!(g, h:h, h′:h′)

pair_half_edges!(g::AbstractRotationGraph, h::AbstractVector{Int},
                 h′::AbstractVector{Int}) =
  set_subpart!(g, vcat(h,h′), :inv, vcat(h′,h))

""" Trace faces of rotation graph, returning list of cycles.
"""
trace_faces(g::AbstractRotationGraph) =
  cycles(h -> σ(g, inv(g, h)), nparts(g, :H))

end
