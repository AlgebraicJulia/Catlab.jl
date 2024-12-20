module Colimits 
export Colimit, AbsColimit, initial, cocone, colimit, pushout,ColimitCocone, 
       CompositeColimit, coproduct, create,copair, proj, coproj1, coproj2, 
      CompositePushout,  NamedColimit, ComposeCoproductCoequalizer

using StructEquality

using .....Theories: dom, codom, universal
import .....Theories: copair, coproj1, coproj2, factorize, proj

using ...Categories: Category
using ...FreeDiagrams
import ...FreeDiagrams: apex, feet, legs
using ...FinFunctors: FinDomFunctor
using ...Diagrams: Diagram

abstract type AbsColimit end


cocone(lim::AbsColimit) = lim.cocone # by default, assume AbsColimit has `cocone` field

apex(lim::AbsColimit) = apex(cocone(lim))

feet(lim::AbsColimit) = feet(cocone(lim))

legs(lim::AbsColimit) = legs(cocone(lim))

Base.iterate(l::AbsColimit, i...) = iterate(cocone(l), i...)

proj(coeq::AbsColimit) = only(legs(coeq))

coproj1(colim::AbsColimit) = let (l,_) = legs(colim); l end

coproj2(colim::AbsColimit) = let (_,l) = legs(colim); l end

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


# Colimit Implementations 
#########################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct ColimitCocone <: AbsColimit
  cocone::Multicospan
end



# Generic colimits
####################

colimit(d::FreeDiagram, m::Category; alg=DefaultColimit())  = 
  colimit(BipartiteFreeDiagram(d; colimit=true), m, alg)

colimit(d::FinDomFunctor; alg=DefaultColimit(), kw...) = 
  colimit(FreeDiagram(d), codom(d); alg, kw...)



# Named colimits
##################




# """
# Apply the universal property of a colimit to a multicospan
# Optionally validate the cospan.
# """
# function universal(c::Colimit, x::Multicospan; check=false)
#   if check
#     co = cocone_objects(c.diag)
#     feet(x) == co || error("Cospan $(feet(x)) doesn't match cocone_objects $co")
#     bp = BipartiteFreeDiagram(getvalue(c.diag); colimit=true)

#     for i in 1:nv₂(bp)
#       allequal(map(incident(bp, i, :tgt)) do j 
#         bp[j, :hom]  ⋅ x[bp[j, :tgt]] 
#       end) || error("Non-commuting cocone for ob₂ $i")
#     end
#   end
#   _universal(getvalue(c.diag), getcategory(c.diag), getvalue(c), x)
# end

# universal(c::Colimit, x::Cospan; check=false) = universal(c, Multicospan(x); check)



# Named universal maps 
######################


function factorize(colim::AbsColimit, h)
  getvalue(colim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(colim, Multicospan([h]))
end


""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(C, colim::AbsColimit, fs::AbstractVector)  =
  universal(C, colim, Multicospan(fs))

copair(C, lim::AbsColimit, f1::T,f2::T) where {T} = 
  copair(C, lim, [f1, f2])
  
# copair(f, g, m::Category) = copair([f,g], m)
# copair(C, fs::AbstractVector)  = 
#   copair(C, coproduct(C, codom.(fs)), fs)

end # module
