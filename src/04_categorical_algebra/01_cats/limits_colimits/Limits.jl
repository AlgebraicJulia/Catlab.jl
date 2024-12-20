module Limits

export Limit, cone, limit,LimitCone, proj1, proj2, pair
       
using StructEquality

using .....Theories: dom, codom
import .....Theories: universal
import .....Theories: pair, proj1, proj2, incl

using ...Categories: Category
using ...FreeDiagrams
import ...FreeDiagrams: apex, feet, legs
using ...FinFunctors: FinDomFunctor
using ...Diagrams: Diagram

abstract type AbsLimit end



cone(lim::AbsLimit) = lim.cone # by default, assume AbsLimit has `cone` field

apex(lim::AbsLimit) = apex(cone(lim))

feet(lim::AbsLimit) = feet(cone(lim))

legs(lim::AbsLimit) = legs(cone(lim))

Base.iterate(l::AbsLimit, i...) = iterate(cone(l), i...)

incl(lim::AbsLimit) = only(legs(lim))

proj1(lim::AbsLimit) = let (l,_) = legs(lim); l end

proj2(lim::AbsLimit) = let (_,l) = legs(lim); l end

Base.length(lim::AbsLimit) = length(cone(lim))

# Algorithms
############

abstract type LimitAlgorithm end 

@struct_hash_equal struct DefaultLimit <: LimitAlgorithm end

# abstract type CatAbsLimit{Ob,Hom} end


""" Algorithm for limit of cospan or multicospan with feet being finite sets.

In the context of relational databases, such limits are called *joins*. The
trivial join algorithm is [`NestedLoopJoin`](@ref), which is algorithmically
equivalent to the generic algorithm `ComposeProductEqualizer`. The algorithms
[`HashJoin`](@ref) and [`SortMergeJoin`](@ref) are usually much faster. If you
are unsure what algorithm to pick, use [`SmartJoin`](@ref).
"""
abstract type JoinAlgorithm <: LimitAlgorithm end

""" Compute pullback by composing a product with an equalizer.

See also: [`ComposeCoproductCoequalizer`](@ref).
"""
@struct_hash_equal struct ComposeProductEqualizer <: LimitAlgorithm end 

# Limit Implementations 
#######################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct LimitCone <: AbsLimit
  cone::Multispan
end


# Generic limits
####################

limit(d::FreeDiagram, m::Category; alg=DefaultLimit()) = 
  limit(BipartiteFreeDiagram{Ob,Hom}(d; colimit=false), m, alg)

limit(d::FinDomFunctor; alg=DefaultLimit(), kw...) = 
  limit(FreeDiagram(d), codom(d); alg, kw...)



# Universal interface
#####################

# """ Coerce spans to multispans when calling `universal` """
# universal(C, P, s::Span) = universal(C, P, Multispan(s))  


# THIS CHECK CODE COULD STILL BE USEFUL
# if check
#   co = cone_objects(c.diag)
#   feet(x) == co || error("Span $(feet(x)) doesn't match cone_objects $co")
#   bp = BipartiteFreeDiagram(getvalue(c.diag); colimit=false)

#   for i in 1:nv₁(bp)
#     allequal(map(incident(bp, i, :src)) do j 
#       x[bp[j, :tgt]] ⋅ bp[j, :hom]
#     end) || error("Non-commuting cone for ob₁ $i")
#   end
# end
# _universal(getvalue(c.diag), getcategory(c.diag), getvalue(c), x)
# universal(c::AbsLimit, x::Span; check=false) = universal(c, Multispan(x); check)

# Named universal maps (for no particular Limit kind)
#####################################################

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(C, lim::AbsLimit, fs::AbstractVector) = universal(C, lim, Multispan(fs))

pair(C, lim::AbsLimit, f1::T, f2::T) where {T} = pair(C, lim, [f1, f2])


end # module
