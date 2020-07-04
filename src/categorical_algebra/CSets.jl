""" Computing with C-sets (presheaves).
"""
module CSets
export AbstractCSet, CSet, CSetType, nparts, subpart, incident, add_part!,
  set_subpart!, set_subparts!

using Compat
using LabelledArrays, StaticArrays

using ...Syntax, ...Present
using ...Theories: Category, FreeCategory, dom, codom, compose, id

# C-sets
########

abstract type AbstractCSet{Ob,Hom,Dom,Codom} end

""" Data type for C-sets (presheaves).

To ensure consistency, the fields of the struct should never be mutated
directly. As in LightGraphs.jl, the incidence vectors are kept in sorted order.
"""
mutable struct CSet{Ob,Hom,Dom,Codom,Index,NOb,NHom,NIndex} <:
       AbstractCSet{Ob,Hom,Dom,Codom}
  nparts::SLArray{Tuple{NOb},Int,1,NOb,Ob}
  subparts::SLArray{Tuple{NHom},Vector{Int},1,NHom,Hom}
  incident::SLArray{Tuple{NIndex},Vector{Vector{Int}},1,NIndex,Index}
end

function CSet{Ob,Hom,Dom,Codom}() where {Ob,Hom,Dom,Codom}
  CSet{Ob,Hom,Dom,Codom,Hom}()
end
function CSet{Ob,Hom,Dom,Codom,Index}() where {Ob,Hom,Dom,Codom,Index}
  NOb, NHom, NIndex = length(Ob), length(Hom), length(Index)
  @assert length(Dom) == NHom && length(Codom) == NHom
  CSet{Ob,Hom,Dom,Codom,Index,NOb,NHom,NIndex}(
    SLArray{Tuple{NOb},Ob}(zeros(SVector{NOb,Int})),
    SLArray{Tuple{NHom},Hom}(copies(SVector{NHom,Vector{Int}})),
    SLArray{Tuple{NIndex},Index}(copies(SVector{NIndex,Vector{Vector{Int}}})))
end

""" Create C-set data type from presentation of category.
"""
function CSetType(pres::Presentation{Category}; index=nothing)
  obs, homs = generators(pres, :Ob), generators(pres, :Hom)
  CSet{Tuple(nameof.(obs)),
       Tuple(nameof.(homs)),
       Tuple(findfirst(obs .== dom(hom)) for hom in homs),
       Tuple(findfirst(obs .== codom(hom)) for hom in homs),
       Tuple(isnothing(index) ? nameof.(homs) : index)}
end

function Base.:(==)(x1::T, x2::T) where T <: CSet
  # The incidence data is redundant, so need not be compared.
  x1.nparts == x2.nparts && x1.subparts == x2.subparts
end

nparts(cset::CSet, type) = cset.nparts[type]

function subpart(cset::CSet, part::Union{Int,AbstractVector{Int}}, name)
  # Allow both single and vectorized access.
  cset.subparts[name][part]
end

incident(cset::CSet, part::Int, name) = cset.incident[name][part]

""" Add part of given type to C-set, optionally setting its subparts.
"""
add_part!(cset::CSet, type) = add_part!(cset, type, NamedTuple())
add_part!(cset::CSet, type, subparts) = _add_part!(cset, Val(type), subparts)

@generated function _add_part!(cset::CSet{obs,homs,doms,codoms,indexed},
    ::Val{type}, subparts) where {obs,homs,doms,codoms,indexed,type}
  ob = NamedTuple{obs}(eachindex(obs))[type]
  in_homs = Tuple(homs[i] for (i, codom) in enumerate(codoms)
                  if codom == ob && homs[i] ∈ indexed)
  out_homs = Tuple(homs[i] for (i, dom) in enumerate(doms) if dom == ob)
  quote
    part = cset.nparts.$type + 1
    cset.nparts = SLVector(cset.nparts; $type=part)
    for name in $(in_homs)
      push!(cset.incident[name], Int[])
    end
    for name in $(out_homs)
      push!(cset.subparts[name], 0)
    end
    set_subparts!(cset, part, subparts)
    part
  end
end

""" Mutate subpart of a part in a C-set.

See also: [`set_subparts!`](@ref).
"""
function set_subpart!(cset::CSet, part, name, subpart)
  _set_subpart!(cset, part, Val(name), subpart)
end
@generated function _set_subpart!(cset::CSet{obs,homs,doms,codoms,indexed},
    part, ::Val{name}, subpart) where {obs,homs,doms,codoms,indexed,name}
  if name ∈ indexed
    quote
      old = cset.subparts.$name[part]
      cset.subparts.$name[part] = subpart
      if old > 0
        deletesorted!(cset.incident.$name[old], part)
      end
      if subpart > 0
        insertsorted!(cset.incident.$name[subpart], part)
      end
    end
  else
    quote
      cset.subparts.$name[part] = subpart
    end
  end
end

""" Mutate subparts of a part in a C-set.

See also: [`set_subpart!`](@ref).
"""
function set_subparts!(cset::CSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(cset, part, name, subpart)
  end
end

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  @assert i <= length(a) && a[i] == x "Value $x is not contained in $a"
  deleteat!(a, i)
end

# Graphs
########

import LightGraphs
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
const AbstractGraph = supertype(Graph)

nv(g::AbstractGraph) = nparts(g, :V)
ne(g::AbstractGraph) = nparts(g, :E)
ne(g::AbstractGraph, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

edges(g::AbstractGraph) = 1:ne(g)
edges(g::AbstractGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractGraph, v::Int) = 1 <= v <= nv(g)
has_edge(g::AbstractGraph, e::Int) = 1 <= e <= ne(g)
has_edge(g::AbstractGraph, src::Int, tgt::Int) = tgt ∈ outneighbors(g, src)

add_vertex!(g::AbstractGraph) = add_part!(g, :V)

function add_vertices!(g::AbstractGraph, n::Int)
  for i in 1:n
    add_vertex!(g)
  end
end

add_edge!(g::AbstractGraph, src::Int, tgt::Int) =
  add_part!(g, :E, (src=src, tgt=tgt))

neighbors(g::AbstractGraph, v::Int) = outneighbors(g, v)
inneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :tgt), :src)
outneighbors(g::AbstractGraph, v::Int) = subpart(g, incident(g, v, :src), :tgt)
all_neighbors(g::AbstractGraph, v::Int) =
  Iterators.flatten((inneighbors(g, v), outneighbors(g, v)))

function LightGraphs.SimpleDiGraph(g::AbstractGraph)
  lg = LightGraphs.SimpleDiGraph(nv(g))
  for e in edges(g)
    add_edge!(lg, subpart(g, e, :src), subpart(g, e, :tgt))
  end
  lg
end

# Symmetric graphs
##################

@present TheorySymmetricGraph(FreeCategory) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
  inv::Hom(E,E)

  compose(inv,inv) == id(E)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

# Don't index `inv` because it is self-inverse and don't index `tgt`
# because `src` contains the same information due to symmetry of graph.
const SymmetricGraph = CSetType(TheorySymmetricGraph, index=[:src])
const AbstractSymmetricGraph = supertype(SymmetricGraph)

# In implementing the LightGraphs API, regard edge pairs as a single edge.
nv(g::AbstractSymmetricGraph) = nparts(g, :V)
ne(g::AbstractSymmetricGraph) = nparts(g, :E) ÷ 2
ne(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  count(subpart(g, e, :tgt) == tgt for e in incident(g, src, :src))

edges(g::AbstractSymmetricGraph) = 1:nparts(g, :E)
edges(g::AbstractSymmetricGraph, src::Int, tgt::Int) =
  (e for e in incident(g, src, :src) if subpart(g, e, :tgt) == tgt)

has_vertex(g::AbstractSymmetricGraph, v::Int) = 1 <= v <= nparts(g, :V)
has_edge(g::AbstractSymmetricGraph, e::Int) = 1 <= e <= nparts(g, :E)
has_edge(g::AbstractSymmetricGraph, src::Int, tgt::Int) = tgt ∈ neighbors(g, src)

add_vertex!(g::AbstractSymmetricGraph) = add_part!(g, :V)

function add_vertices!(g::AbstractSymmetricGraph, n::Int)
  for i in 1:n
    add_vertex!(g)
  end
end

function add_edge!(g::AbstractSymmetricGraph, src::Int, tgt::Int)
  e1 = nparts(g, :E) + 1
  e2 = e1 + 1
  add_part!(g, :E, (src=src, tgt=tgt, inv=e2))
  add_part!(g, :E, (src=tgt, tgt=src, inv=e1))
  (e1, e2)
end

neighbors(g::AbstractSymmetricGraph, v::Int) =
  subpart(g, incident(g, v, :src), :tgt)
inneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
outneighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)
all_neighbors(g::AbstractSymmetricGraph, v::Int) = neighbors(g, v)

function LightGraphs.SimpleGraph(g::AbstractSymmetricGraph)
  lg = LightGraphs.SimpleGraph(nv(g))
  for e in edges(g)
    add_edge!(lg, subpart(g, e, :src), subpart(g, e, :tgt))
  end
  lg
end

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
