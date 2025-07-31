module Colimits 
export Colimit, AbsColimit, initial, cocone, colimit, pushout,ColimitCocone, 
       CompositeColimit, coproduct, create, proj, coproj1, coproj2, 
      CompositePushout,  NamedColimit, ComposeCoproductCoequalizer, ThCategoryColimitBase

using StructEquality
using GATlab

using .....Theories: dom, codom
import .....Theories: coproj1, coproj2, factorize, proj, ob, universal

using ...Categories: Category, ThCategoryExplicitSets
using ...FreeDiagrams
import ...FreeDiagrams: apex, feet, legs
using ...FinFunctors: FinDomFunctor
import ..Limits: diagram

"""
Colimit should be sent to AbsColimit.
Legs should be sent to Vector{Hom} for whatever Hom is.
"""
@theory ThCategoryColimitBase <: ThCategoryExplicitSets begin 
  Colimit()::TYPE{AbsColimit}
  ob(colim::Colimit)::Ob

  MCospan::TYPE{Multicospan} # type of (multi)cospans
  apex(s::MCospan)::Ob # apex of the cospan
  cocone(l::Colimit)::MCospan
  apex(cocone(l)) == ob(l) ⊣ [l::Colimit]
end

apex(::WithModel, m::Multicospan; context=nothing) = 
  apex(m; context) # always use dispatch


"""
`AbsColimit` implementations should be able to recover the (free) diagram that
it is a colimit of and a computed colimit cocone.
"""
abstract type AbsColimit end


cocone(lim::AbsColimit) = lim.cocone # by default, assume AbsColimit has `cocone` field
""" We assume *every model* is going to implement `cone` the following way """
cocone(::WithModel, lim::AbsColimit; context=nothing) = cocone(lim)

ob(lim::AbsColimit) = apex(lim)

apex(lim::AbsColimit) = apex(cocone(lim))

feet(lim::AbsColimit) = feet(cocone(lim))

legs(lim::AbsColimit) = legs(cocone(lim))

Base.iterate(l::AbsColimit, i...) = iterate(cocone(l), i...)

proj(coeq::AbsColimit) = only(legs(coeq))

coproj1(colim::AbsColimit) = let (l,_) = legs(colim); l end

coproj2(colim::AbsColimit) = let (_,l) = legs(colim); l end

ob(::WithModel, x::AbsColimit; context=nothing) = ob(x) # always use dispatch


@struct_hash_equal struct ColimitCocone <: AbsColimit 
  cocone::Multicospan
  diagram::FreeDiagram
end 

ob(c::ColimitCocone) = apex(c.cocone)

cocone(c::ColimitCocone) = c.cocone

diagram(c::ColimitCocone) = c.diagram

""" 
By default, computing a universal property with a limit will pull out the
diagram type so that we can dispatch on it
"""
universal(m::WithModel, d::AbsColimit, s::Multicospan; context=nothing) = 
  universal(m, d, getvalue(diagram(d)), s; context)

# Colimit algorithms
######################

abstract type ColimitAlgorithm end 

@struct_hash_equal struct DefaultColimit <: ColimitAlgorithm end


""" Compute pushout by composing a coproduct with a coequalizer.

See also: [`ComposeProductEqualizer`](@ref).
"""
@struct_hash_equal struct ComposeCoproductCoequalizer <: ColimitAlgorithm end 

""" Compute colimit of finite sets whose elements are meaningfully named.

This situation seems to be mathematically uninteresting but is practically
important. The colimit is computed by reduction to the skeleton of **FinSet**
(`FinSet{Int}`) and the names are assigned afterwards, following some reasonable
conventions and add tags where necessary to avoid name clashes.
"""
@struct_hash_equal struct NamedColimit <: ColimitAlgorithm end 

# Generic colimits
####################

"""Not a specific limit: look at the diagram type """
colimit(m::WithModel, d::FreeDiagram; context=nothing)  = 
  colimit(m, getvalue(specialize(d; colimit=true)); context)

# Named universal maps 
######################

# function factorize(C::WithModel, colim::AbsColimit, h)
#   getvalue(diagram(colim)) isa ParallelMorphisms || error(
#     "Can only call `factorize` on ParallelMorphisms colimits")
#   universal[C](colim, Multicospan([h]))
# end


end # module
