module ComposableHoms
export ComposablePair, ComposableMorphisms

using StaticArrays: StaticVector, SVector
using StructEquality
using GATlab 

import .....Theories: dom, codom, ThCategory
using .....BasicSets: FinSet
using ...FreeDiagrams: ThFreeDiagram, FreeDiagram
import ...FreeDiagrams: fmap, specialize

# Note: like for (co)spans, we should independently store the objects in case 
# we do not have type dispatch dom/codom methods for the homs.

""" Composable morphisms in a category.

Composable morphisms are a sequence of morphisms in a category that form a path
in the underlying graph of the category.

For the common special case of two morphisms, see [`ComposablePair`](@ref).
"""
@struct_hash_equal struct ComposableMorphisms{Ob,Hom,Homs<:AbstractVector{Hom}}
  homs::Homs
end

""" Infer types """
function ComposableMorphisms(homs::AbstractVector{Hom}; kw...) where Hom
  Ob = Union{typeof.([dom.(homs); codom(last(homs))])...}
  ComposableMorphisms{Ob, Hom}(homs; kw...)
end

function ComposableMorphisms{Ob,Hom}(homs::Homs; cat=nothing) where {Ob, Hom, Homs<:AbstractVector{Hom}}
  isempty(homs) && error("Composable morphisms must be nonempty")
  𝒞 = isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat

  doms, codoms = dom[𝒞].(homs), codom[𝒞].(homs)
  all(x -> x isa Ob, doms) || error("Not all doms are $Ob")
  last(codoms) isa Ob || error("Not all codoms are $Ob")
  all(c == d for (c,d) in zip(codoms[1:end-1], doms[2:end])) || error(
    "Domain mismatch in composable sequence: $homs")
  ComposableMorphisms{Ob,Hom,Homs}(homs)
end

dom(comp::ComposableMorphisms) = dom(first(comp))

codom(comp::ComposableMorphisms) = codom(last(comp))

hom(comp::ComposableMorphisms) = comp.homs

Base.iterate(comp::ComposableMorphisms, args...) = iterate(comp.homs, args...)

Base.eltype(comp::ComposableMorphisms) = eltype(comp.homs)

Base.length(comp::ComposableMorphisms) = length(comp.homs)

Base.getindex(comp::ComposableMorphisms, i) = comp.homs[i]

Base.firstindex(comp::ComposableMorphisms) = firstindex(comp.homs)

Base.lastindex(comp::ComposableMorphisms) = lastindex(comp.homs)

objects(p::ComposableMorphisms) = [dom(p), codom.(hom(p))...]

""" Apply hom map to the homs """
fmap(d::ComposableMorphisms, _, h, O::Type, H::Type) = ComposableMorphisms(Vector{H}(h.(d)))  


""" Pair of composable morphisms in a category.

[Composable pairs](https://ncatlab.org/nlab/show/composable+pair) are a common
special case of [`ComposableMorphisms`](@ref).
"""
const ComposablePair{Ob,Hom} = ComposableMorphisms{Ob,Hom,<:StaticVector{2,Hom}}


# Constructor in which we infer Hom and Ob type
ComposablePair(f::Hom, g::Hom; kw...) where Hom = ComposablePair{Hom}(f, g; kw...)

# Constructor in which we infer Ob type
function ComposablePair{Hom}(first::Hom, last::Hom; cat=nothing) where Hom
  𝒞 = isnothing(cat) ? Dispatch(ThCategory, [Union{},Hom]) : cat
  Ob = Union{typeof.([dom[𝒞](first), dom[𝒞](last), codom[𝒞](last)])...}
  ComposableMorphisms{Ob, Hom}(SVector(first, last); cat)
end

@instance ThFreeDiagram{Int,Int,Ob,Hom} [model::ComposableMorphisms{Ob,Hom}
                                        ] where {Ob, Hom} begin
  src(x::Int)::Int = x
  tgt(x::Int)::Int = x+1
  obmap(x::Int)::Ob = x == 1 ? dom(model[x]) : codom(model[x-1])
  hommap(i::Int)::Hom = model[i]
  obset()::FinSet = FinSet(length(model)+1)
  homset()::FinSet = FinSet(length(model))
end

function specialize(::Type{ComposableMorphisms}, d::FreeDiagram)
  o, h, os = obset(d), homset(d), ob(d)
  srcs, tgts = src.(Ref(d), h), tgt.(Ref(d), h)
  start = setdiff(srcs,tgts)
  ComposableMorphisms() # KBTODO
end

end # module
