module Limits

export Limit, diagram, cone, limit,LimitCone, proj1, proj2, AbsLimit, 
       JoinAlgorithm, ThCategoryLimitBase, ThCategoryWithLimits, incl
       
using StructEquality
using GATlab

using .....Theories: dom, codom
import .....Theories: universal, ob
import .....Theories: proj1, proj2, incl

using ...Categories: Category, ThCategoryExplicitSets
using ...FreeDiagrams
import ...FreeDiagrams: apex, feet, legs
using ...FinFunctors: FinDomFunctor

@theory ThCategoryLimitBase <: ThCategoryExplicitSets begin
  Limit()::TYPE{AbsLimit}
  ob(lim::Limit)::Ob

  MSpan::TYPE{Multispan} # type of (multi)spans
  apex(s::MSpan)::Ob 
  cone(l::Limit)::MSpan
  apex(cone(l)) == ob(l) ⊣ [l::Limit]
end

apex(::WithModel, m::Multispan; context=nothing) = apex(m) # always use dispatch

"""
`AbsLimit` implementations should be able to recover the diagram that it is a 
limit of and a computed limit cone.

Any implementation must provide 
- cone()::Multispan 
- diagram()::FreeDiagram

Every use of a AbsLimit (e.g. in `universal`) must use these 
methods or the methods below which are derived from these.
"""
abstract type AbsLimit end

cone(lim::AbsLimit) = lim.cone # by default, assume AbsLimit has a `cone` field
""" We assume *every model* is going to implement `cone` the following way """
cone(::WithModel, lim::AbsLimit; context=nothing) = cone(lim)

diagram(lim::AbsLimit) = lim.diagram # by default, assume a `diagram` field

apex(lim::AbsLimit) = apex(cone(lim))

ob(lim::AbsLimit) = apex(lim)

feet(lim::AbsLimit) = feet(cone(lim))

legs(lim::AbsLimit) = legs(cone(lim))

Base.iterate(l::AbsLimit, i...) = iterate(cone(l), i...)

incl(lim::AbsLimit) = only(legs(lim))

proj1(lim::AbsLimit) = let (l,_) = legs(lim); l end

proj2(lim::AbsLimit) = let (_,l) = legs(lim); l end

Base.length(lim::AbsLimit) = length(cone(lim))

ob(::WithModel, x::AbsLimit; context=nothing) = apex(x) # always use dispatch

""" 
By default, computing a universal property with a limit will pull out the
diagram type so that we can dispatch on it
"""
universal(m::WithModel, d::AbsLimit, s::Multispan; context=nothing) = 
  universal(m, d, getvalue(diagram(d)), s; context)

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
  diagram::FreeDiagram
end

diagram(c::LimitCone) = c.diagram  

# Generic limits
####################

function limit end

end # module
