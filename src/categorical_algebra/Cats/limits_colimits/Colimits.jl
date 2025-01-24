module Colimits 
export AbstractColimit, Colimit, ColimitAlgorithm, SpecializeColimit, cocone, 
       colimit, universal

using StaticArrays: StaticVector, SVector
using StructEquality


using ...FreeDiagrams, ...FinCats, ...FinFunctors
import ...FreeDiagrams: legs, apex
import ..LimitsColimits: ob, universal


""" Abstract type for colimit in a category.

The standard concrete subtype is [`Colimit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractColimit{Ob,Diagram} end

ob(colim::AbstractColimit) = apex(colim)
cocone(colim::AbstractColimit) = colim.cocone
apex(colim::AbstractColimit) = apex(cocone(colim))
legs(colim::AbstractColimit) = legs(cocone(colim))

Base.iterate(colim::AbstractColimit, args...) = iterate(cocone(colim), args...)
Base.eltype(colim::AbstractColimit) = eltype(cocone(colim))
Base.length(colim::AbstractColimit) = length(cocone(colim))

""" Colimit in a category.
"""
@struct_hash_equal struct Colimit{Ob,Diagram,Cocone<:Multicospan{Ob}} <:
    AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
end


""" Algorithm for computing colimits.
"""
abstract type ColimitAlgorithm end



""" Colimit of a diagram.

To define colimits in a category with objects `Ob`, override the method
`colimit(::FreeDiagram{Ob})` for general colimits or `colimit(::D)` with
suitable type `D <: FixedShapeFreeDiagram{Ob}` for colimits of specific shape,
such as coproducts or coequalizers.

See also: [`limit`](@ref)
"""
colimit(diagram; kw...) = colimit(diagram_type(diagram), diagram; kw...)
colimit(diagram, ::Nothing; kw...) = colimit(diagram; kw...) # alg == nothing


""" Meta-algorithm that reduces general colimits to common special cases.

Dual to [`SpecializeLimit`](@ref).
"""
@Base.kwdef struct SpecializeColimit <: ColimitAlgorithm
  fallback::Union{ColimitAlgorithm,Nothing} = nothing
end

colimit(diagram, alg::SpecializeColimit) = colimit(diagram, alg.fallback)

function colimit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
                 alg::SpecializeColimit) where {Ob,Hom}
  if is_discrete(dom(F))
    colimit(DiscreteDiagram(collect_ob(F), Hom), SpecializeColimit())
  else
    colimit(F, alg.fallback)
  end
end
colimit(diagram::FreeDiagram, alg::SpecializeColimit) =
  colimit(FinDomFunctor(diagram), alg)

function colimit(Xs::DiscreteDiagram{Ob,Hom,Obs},
                 alg::SpecializeColimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    colimit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), SpecializeColimit())
  else
    colimit(Xs, alg.fallback)
  end
end

end # module
