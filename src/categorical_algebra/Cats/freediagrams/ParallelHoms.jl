module ParallelHoms
export ParallelPair, ParallelMorphisms

using StaticArrays: StaticVector, SVector
using StructEquality

using ..FreeDiagrams
import ..FreeDiagrams: ob, hom, dom, codom, cone_objects, cocone_objects

# Parallel morphisms
#-------------------

""" Parallel morphims in a category.

[Parallel morphisms](https://ncatlab.org/nlab/show/parallel+morphisms) are just
morphisms with the same domain and codomain. A (co)limit of this shape is a
(co)equalizer.

For the common special case of two morphisms, see [`ParallelPair`](@ref).
"""
@struct_hash_equal struct ParallelMorphisms{Dom,Codom,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Union{Dom,Codom},Hom}
  dom::Dom
  codom::Codom
  homs::Homs
end

function ParallelMorphisms(homs::AbstractVector)
  @assert !isempty(homs) && allequal(dom.(homs)) && allequal(codom.(homs))
  ParallelMorphisms(dom(first(homs)), codom(first(homs)), homs)
end

""" Pair of parallel morphisms in a category.

A common special case of [`ParallelMorphisms`](@ref).
"""
const ParallelPair{Dom,Codom,Hom} =
  ParallelMorphisms{Dom,Codom,Hom,<:StaticVector{2,Hom}}

function ParallelPair(first, last)
  dom(first) == dom(last) ||
    error("Domains of parallel pair do not match: $first vs $last")
  codom(first) == codom(last) ||
    error("Codomains of parallel pair do not match: $first vs $last")
  ParallelMorphisms(dom(first), codom(first), SVector(first, last))
end

dom(para::ParallelMorphisms) = para.dom
codom(para::ParallelMorphisms) = para.codom
hom(para::ParallelMorphisms) = para.homs

cone_objects(para::ParallelMorphisms) = SVector(dom(para))
cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

Base.iterate(para::ParallelMorphisms, args...) = iterate(para.homs, args...)
Base.eltype(para::ParallelMorphisms) = eltype(para.homs)
Base.length(para::ParallelMorphisms) = length(para.homs)
Base.getindex(para::ParallelMorphisms, i) = para.homs[i]
Base.firstindex(para::ParallelMorphisms) = firstindex(para.homs)
Base.lastindex(para::ParallelMorphisms) = lastindex(para.homs)

allequal(xs::AbstractVector) = isempty(xs) || all(==(xs[1]), xs)

end # module