
module ParallelHoms 
export ParallelMorphisms, ParallelPair

using StaticArrays: StaticVector, SVector

using StructEquality
using GATlab 

using .....BasicSets: FinSet
using ...FreeDiagrams: ThFreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects

import .ThCategory: dom, codom

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
fmap(d::ParallelMorphisms, o, h) = 
  ParallelMorphisms(o(d.dom), o(d.codom), h.(d.homs))


function ParallelMorphisms(xs::Hs) where {H, Hs<:AbstractVector{H}}
  isempty(xs) && error("Parallel morphisms must be nonempty")
  allequal(dom.(xs)) || error("Parallel morphism must share domain")
  allequal(codom.(xs)) || error("Parallel morphism must share domain")
  d, c = dom(first(xs)), codom(first(xs))
  Ob = Union{typeof(d), typeof(c)}
  ParallelMorphisms{Ob,H,Hs}(d, c, xs)
end

ParallelPair(first, last) =  ParallelMorphisms(SVector(first, last))

@instance ThFreeDiagram{Bool,Int,Ob,Hom,FinSet
                       } [model::ParallelMorphisms{Ob,Hom}] where {Ob, Hom} begin
  src(::Int)::Int = true
  tgt(::Int)::Int = false
  obmap(x::Bool)::Ob = x ? dom(model) : codom(model)
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet([true, false])
  homset()::FinSet = FinSet(length(model))
end


end # module 