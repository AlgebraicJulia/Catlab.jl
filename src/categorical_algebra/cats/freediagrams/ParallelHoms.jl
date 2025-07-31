
module ParallelHoms 
export ParallelMorphisms, ParallelPair

using StaticArrays: StaticVector, SVector

using StructEquality
using GATlab 

import .....Theories: dom, codom, hom, ThCategory
using .....BasicSets: FinSet
using ...FreeDiagrams: ThFreeDiagram, FreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects, specialize


@struct_hash_equal struct ParallelMorphisms{Ob, Hom, Homs<:AbstractVector{Hom}}
  dom::Ob
  codom::Ob
  homs::Homs
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Ob,Hom} = ParallelMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

Base.length(m::ParallelMorphisms) = length(m.homs) 

Base.iterate(m::ParallelMorphisms, x...) = iterate(m.homs, x...)

Base.getindex(m::ParallelMorphisms, x) = m.homs[x]

Base.lastindex(m::ParallelMorphisms) = lastindex(m.homs)

dom(p::ParallelMorphisms) = p.dom

codom(p::ParallelMorphisms) = p.codom

hom(comp::ParallelMorphisms) = comp.homs

objects(p::ParallelMorphisms) = [dom(p), codom(p)]

cone_objects(para::ParallelMorphisms) = SVector(dom(para))

cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

""" Replace objects and homs via functions """
fmap(d::ParallelMorphisms, o, h, O::Type, H::Type) = 
  ParallelMorphisms(o(d.dom)::O, o(d.codom)::O, Vector{H}(h.(d.homs)))


function ParallelMorphisms(xs::Hs; cat=nothing) where {H, Hs<:AbstractVector{H}}
  isempty(xs) && error("Parallel morphisms must be nonempty")
  𝒞 = isnothing(cat) ? Dispatch(ThCategory, [typeof(dom(first(xs))), H]) : cat
  d, c = dom[𝒞](first(xs)), codom[𝒞](first(xs))
  Ob = Union{typeof(d), typeof(c)}
  allequal(dom[𝒞].(xs)) || error(
      "Parallel morphism must share domain $(dom[𝒞].(xs))")
  allequal(codom[𝒞].(xs)) || error(
    "Parallel morphism must share domain $(codom[𝒞].(xs))")
  ParallelMorphisms{Ob,H,Hs}(d, c, xs)
end

ParallelPair(first, last) =  ParallelMorphisms(SVector(first, last))

@instance ThFreeDiagram{Bool,Int,Ob,Hom} [model::ParallelMorphisms{Ob,Hom}
                                         ] where {Ob, Hom} begin
  src(::Int)::Int = true
  tgt(::Int)::Int = false
  obmap(x::Bool)::Ob = x ? dom(model) : codom(model)
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet([true, false])
  homset()::FinSet = FinSet(length(model))
end

function specialize(::Type{ParallelMorphisms}, d::FreeDiagram)
  s, t = src(d, first(homset(d))), tgt(d, first(homset(d)))
  ParallelMorphisms(ob_map(d, s), ob_map(d, t), hom(d))
end

end # module 