""" Embedded graphs, represented as C-sets.

The term *embedded graph* is used as in topological graph theory, graph drawing,
and related fields to mean a combinatorial structure representing a graph
embedded in an (oriented) surface, up to equivalence under
(orientation-preserving) homeomorphism.
"""
module EmbeddedGraphs
export AbstractRotationGraph, RotationGraph, σ, add_corolla!, pair_half_edges!,
  AbstractRotationSystem, RotationSystem, α, trace_vertices, trace_faces

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

σ(x::AbstractACSet, args...) = subpart(x, args..., :σ)

""" Add corolla to rotation graph or system.

A *corolla* is a vertex together with its incident half-edges, the number of
which is its *valence*. The rotation on the half-edges is the consecutive one
induced by the half-edge part numbers.
"""
function add_corolla!(g::AbstractRotationGraph, valence::Int; kw...)
  v = add_vertex!(g; kw...)
  n = nparts(g, :H)
  add_parts!(g, :H, valence; vertex=v, σ=circshift((n+1):(n+valence), -1))
end

pair_half_edges!(g::AbstractRotationGraph, h::Int, h′::Int) =
  pair_half_edges!(g, h:h, h′:h′)
pair_half_edges!(g::AbstractRotationGraph, h::AbstractVector{Int},
                 h′::AbstractVector{Int}) =
  set_subpart!(g, vcat(h,h′), :inv, vcat(h′,h))

function trace_faces(g::AbstractRotationGraph)
  ϕ = sortperm(inv(g)[σ(g)]) # == (σ ⋅ inv)⁻¹
  cycles(ϕ)
end

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

α(x::AbstractACSet, args...) = subpart(x, args..., :α)

function add_corolla!(sys::AbstractRotationSystem, valence::Int)
  n = nparts(sys, :H)
  add_parts!(sys, :H, valence; σ=circshift((n+1):(n+valence), -1))
end

pair_half_edges!(sys::AbstractRotationSystem, h::Int, h′::Int) =
  pair_half_edges!(sys, h:h, h′:h′)
pair_half_edges!(sys::AbstractRotationSystem, h::AbstractVector{Int},
                 h′::AbstractVector{Int}) =
  set_subpart!(sys, vcat(h,h′), :α, vcat(h′,h))

""" Trace vertices of rotation system, returning a list of cycles.
"""
trace_vertices(sys::AbstractRotationSystem) = cycles(σ(sys))

""" Trace faces of rotation system, returning list of cycles.
"""
function trace_faces(sys::AbstractRotationSystem)
  ϕ = sortperm(α(sys)[σ(sys)]) # == (σ⋅α)⁻¹ == α⁻¹ ⋅ σ⁻¹
  cycles(ϕ)
end

end
