""" Computing with C-sets (presheaves).
"""
module CSets
export CSet, nparts, subpart, incident, add_part!

using AutoHashEquals
using LabelledArrays, StaticArrays

using ...Syntax, ...Present
using ...Theories: Category, FreeCategory, dom, codom

# C-sets
########

@auto_hash_equals mutable struct CSet{Ob,Hom,Dom,Codom,NOb,NHom}
  nparts::SLArray{Tuple{NOb},Int,1,NOb,Ob}
  subparts::SLArray{Tuple{NHom},Vector{Int},1,NHom,Hom}
  incident::SLArray{Tuple{NHom},Vector{Vector{Int}},1,NHom,Hom}
end

function CSet{Ob,Hom,Dom,Codom}() where {Ob,Hom,Dom,Codom}
  NOb, NHom = length(Ob), length(Hom)
  @assert length(Dom) == NHom && length(Codom) == NHom
  CSet{Ob,Hom,Dom,Codom,NOb,NHom}(
    SLArray{Tuple{NOb},Ob}(zeros(SVector{NOb,Int})),
    SLArray{Tuple{NHom},Hom}(copies(SVector{NHom,Vector{Int}})),
    SLArray{Tuple{NHom},Hom}(copies(SVector{NHom,Vector{Vector{Int}}})))
end

""" Create C-set data type from presentation of category.
"""
function CSetType(pres::Presentation{Category})
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  CSet{Tuple(nameof.(obs)),
       Tuple(nameof.(homs)),
       Tuple(findfirst(obs .== dom(hom)) for hom in homs),
       Tuple(findfirst(obs .== codom(hom)) for hom in homs)}
end

nparts(cset::CSet, type) = cset.nparts[type]

function subpart(cset::CSet, name, part::Union{Int,AbstractVector{Int}})
  # Allow both single and vectorized access.
  cset.subparts[name][part]
end

incident(cset::CSet, name, part::Int) = cset.incident[name][part]

add_part!(cset::CSet, type) = add_part!(cset, type, NamedTuple())
add_part!(cset::CSet, type, subparts) = _add_part!(cset, Val(type), subparts)

@generated function _add_part!(cset::CSet{obs,homs,doms,codoms}, ::Val{type},
    subparts::NamedTuple{sub}) where {obs,homs,doms,codoms,type,sub}
  ob = NamedTuple{obs}(eachindex(obs))[type]
  out_homs = Tuple(homs[i] for (i, dom) in enumerate(doms) if dom == ob)
  in_homs = Tuple(homs[i] for (i, codom) in enumerate(codoms) if codom == ob)
  @assert sub ⊆ out_homs "Given subparts $sub not among $out_homs"
  undef_out_homs = Tuple(hom for hom in out_homs if hom ∉ sub)

  return quote
    part = cset.nparts.$type + 1
    cset.nparts = SLVector(cset.nparts; $type=part)
    for name in $(in_homs)
      push!(cset.incident[name], Int[])
    end
    for name in $(undef_out_homs)
      push!(cset.subparts[name], 0)
    end
    for (name, subpart) in pairs(subparts)
      push!(cset.subparts[name], subpart)
      push!(cset.incident[name][subpart], part)
    end
    part
  end
end

# Graphs
########

import LightGraphs: nv, ne, edges, has_edge, has_vertex,
  add_edge!, add_vertex!, add_vertices!,
  neighbors, inneighbors, outneighbors, all_neighbors

@present TheoryGraph(FreeCategory) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

const Graph = CSetType(TheoryGraph)

nv(g::Graph) = nparts(g, :V)
ne(g::Graph) = nparts(g, :E)
ne(g::Graph, src::Int, tgt::Int) = count(v == tgt for v in outneighbors(g, src))
has_vertex(g::Graph, v::Int) = 1 <= v <= nv(g)
has_edge(g::Graph, e::Int) = 1 <= e <= ne(g)
has_edge(g::Graph, src::Int, tgt::Int) = tgt ∈ outneighbors(g, src)

add_vertex!(g::Graph) = add_part!(g, :V)
add_vertices!(g::Graph, n::Int) = for i in 1:n; add_vertex!(g) end
add_edge!(g::Graph, src::Int, tgt::Int) = add_part!(g, :E, (src=src, tgt=tgt))

neighbors(g::Graph, v::Int) = outneighbors(g, v)
inneighbors(g::Graph, v::Int) = subpart(g, :src, incident(g, :tgt, v))
outneighbors(g::Graph, v::Int) = subpart(g, :tgt, incident(g, :src, v))
all_neighbors(g::Graph, v::Int) = [ inneighbors(g, v); outneighbors(g, v) ]

# Static arrays
###############

# Make static array of copies of object, using nullary constructor.
# Based on StaticArrays.jl/src/arraymath.jl
@inline copies(::Type{SA}) where {SA <: StaticArray} = _copies(Size(SA), SA)
@generated function _copies(::Size{s}, ::Type{SA}) where {s, SA <: StaticArray}
  T = eltype(SA)
  v = [:($T()) for i = 1:prod(s)]
  return quote
    Base.@_inline_meta
    $SA(tuple($(v...)))
  end
end

end
