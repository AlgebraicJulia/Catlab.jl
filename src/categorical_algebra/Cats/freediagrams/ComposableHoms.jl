module ComposableHoms 
export ComposablePair, ComposableMorphisms

using StaticArrays: StaticVector, SVector
using StructEquality

using ..FreeDiagrams
import ..FreeDiagrams: ob, hom, dom, codom

# Composable morphisms
#---------------------

""" Composable morphisms in a category.

Composable morphisms are a sequence of morphisms in a category that form a path
in the underlying graph of the category.

For the common special case of two morphisms, see [`ComposablePair`](@ref).
"""
@struct_hash_equal struct ComposableMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  homs::Homs
end

function ComposableMorphisms(homs::Homs) where {Hom, Homs<:AbstractVector{Hom}}
  doms, codoms = dom.(homs), codom.(homs)
  all(c == d for (c,d) in zip(codoms[1:end-1], doms[2:end])) ||
    error("Domain mismatch in composable sequence: $homs")
  ComposableMorphisms{Union{eltype(doms),eltype(codoms)},Hom,Homs}(homs)
end

""" Pair of composable morphisms in a category.

[Composable pairs](https://ncatlab.org/nlab/show/composable+pair) are a common
special case of [`ComposableMorphisms`](@ref).
"""
const ComposablePair{Ob,Hom} = ComposableMorphisms{Ob,Hom,<:StaticVector{2,Hom}}

ComposablePair(first, last) = ComposableMorphisms(SVector(first, last))

dom(comp::ComposableMorphisms) = dom(first(comp))
codom(comp::ComposableMorphisms) = codom(last(comp))
hom(comp::ComposableMorphisms) = comp.homs

Base.iterate(comp::ComposableMorphisms, args...) = iterate(comp.homs, args...)
Base.eltype(comp::ComposableMorphisms) = eltype(comp.homs)
Base.length(comp::ComposableMorphisms) = length(comp.homs)
Base.getindex(comp::ComposableMorphisms, i) = comp.homs[i]
Base.firstindex(comp::ComposableMorphisms) = firstindex(comp.homs)
Base.lastindex(comp::ComposableMorphisms) = lastindex(comp.homs)

end # module