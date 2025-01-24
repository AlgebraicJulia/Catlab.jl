module Limits 
export AbstractLimit, Limit, LimitAlgorithm, SpecializeLimit, cone, limit, 
       universal

using StaticArrays: StaticVector, SVector
using StructEquality

using ...FreeDiagrams, ...FinCats, ...FinFunctors
import ...FreeDiagrams: legs, apex
import ..LimitsColimits: ob, universal

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

ob(lim::AbstractLimit) = apex(lim)
cone(lim::AbstractLimit) = lim.cone

"""Synonymous with `ob` in the case of `Limit`s, but 
present here to allow a `Limit` to be implicitly 
treated like a `Multispan`."""
apex(lim::AbstractLimit) = apex(cone(lim)) 
legs(lim::AbstractLimit) = legs(cone(lim))

Base.iterate(lim::AbstractLimit, args...) = iterate(cone(lim), args...)
Base.eltype(lim::AbstractLimit) = eltype(cone(lim))
Base.length(lim::AbstractLimit) = length(cone(lim))

""" Limit in a category.
"""
@struct_hash_equal struct Limit{Ob,Diagram,Cone<:Multispan{Ob}} <:
    AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
end


""" Algorithm for computing limits.
"""
abstract type LimitAlgorithm end


""" Limit of a diagram.

To define limits in a category with objects `Ob`, override the method
`limit(::FreeDiagram{Ob})` for general limits or `limit(::D)` with suitable type
`D <: FixedShapeFreeDiagram{Ob}` for limits of specific shape, such as products
or equalizers.

See also: [`colimit`](@ref)
"""
limit(diagram; kw...) = limit(diagram_type(diagram), diagram; kw...)
limit(diagram, ::Nothing; kw...) = limit(diagram; kw...) # alg == nothing



""" Meta-algorithm that reduces general limits to common special cases.

Reduces limits of free diagrams that happen to be discrete to products. If this
fails, fall back to the given algorithm (if any).

TODO: Reduce free diagrams that are (multi)cospans to (wide) pullbacks.
"""
@Base.kwdef struct SpecializeLimit <: LimitAlgorithm
  fallback::Union{LimitAlgorithm,Nothing} = nothing
end

limit(diagram, alg::SpecializeLimit) = limit(diagram, alg.fallback)

function limit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
               alg::SpecializeLimit) where {Ob,Hom}
  if is_discrete(dom(F))
    limit(DiscreteDiagram(collect_ob(F), Hom), SpecializeLimit())
  else
    limit(F, alg.fallback)
  end
end
limit(diagram::FreeDiagram, alg::SpecializeLimit) =
  limit(FinDomFunctor(diagram), alg)

function limit(Xs::DiscreteDiagram{Ob,Hom,Obs},
               alg::SpecializeLimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    limit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), SpecializeLimit())
  else
    limit(Xs, alg.fallback)
  end
end

end # module
