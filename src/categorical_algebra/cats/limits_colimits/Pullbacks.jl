module Pullbacks
export AbsPullbackLimit, NestedLoopJoin, SortMergeJoin, HashJoin, SmartJoin, pullback, pullback_pair, ThCategoryWithPullbacks, CatWithPullbacks

using StructEquality
using GATlab

import .....Theories: universal, ob
using ...Cats: Category, Multispan, Multicospan, FreeDiagram

using ..LimitsColimits: AbsLimit, ThCategoryLimitBase, JoinAlgorithm, LimitCone,    
                        CatWithEqualizers
import ..Limits: limit, diagram


@theory ThCategoryWithPullbacks <: ThCategoryLimitBase begin
  MCSpan::TYPE{Multicospan}

  limit(d::MCSpan)::Limit
  universal(lim::Limit, d::MCSpan, sp::MSpan)::(apex(sp) → ob(lim))
end

ThCategoryWithPullbacks.Meta.@wrapper CatWithPullbacks

# Algorithms
#############

""" This is the naive algorithm for computing joins. """
@struct_hash_equal struct NestedLoopJoin <: JoinAlgorithm end 

""" [Sort-merge join](https://en.wikipedia.org/wiki/Sort-merge_join) algorithm.
"""
@struct_hash_equal struct SortMergeJoin <: JoinAlgorithm end 

""" [Hash join](https://en.wikipedia.org/wiki/Hash_join) algorithm.
"""
@struct_hash_equal struct HashJoin <: JoinAlgorithm end

""" Meta-algorithm for joins that attempts to pick an appropriate algorithm. """
@struct_hash_equal struct SmartJoin <: JoinAlgorithm end



# Limit data structures 
#######################

# """ Pullback formed as composite of product and equalizer.

# The fields of this struct are an implementation detail; accessing them directly
# violates the abstraction. Everything that you can do with a pullback, including
# invoking its universal property, should be done through the generic interface
# for limits.

# See also: [`CompositePushout`](@ref).
# """
# struct CompositePullback{Hom} <: AbsLimit
#   cone::Multispan
#   prod::LimitCone
#   eq::Hom
# end

# ob(c::CompositePullback) = ob(c.cone)


# """
# `CompositePullback` is constructed via applying the `ComposeProductEqualizer` 
# algorithm to a cospan.
# """
# function composite_pullback(C::CatWithEqualizers, cospan::Multicospan)
#   prod = product(C, feet(cospan))
#   (ι,) = eq = equalizer(C, map(compose[getvalue(m)], legs(prod), legs(cospan)))
#   cone = Multispan(map(π -> compose(C, ι,π), legs(prod)))
#   Limit(CompositePullback(cone, prod, eq), FreeDiagram(cospan))
# end

# function universal(C::CatWithEqualizers, lim::CompositePullback, cone::Multispan; context=nothing)
#   factorize(C, lim.eq, universal(C, lim.prod, cone))
# end

# Named limits / universal properties
#####################################

@model_method pullback

pullback(C::CatWithPullbacks, fs::AbstractVector) = 
  limit[getvalue(C)](Multicospan(fs; cat=getvalue(C)))

pullback(C::CatWithPullbacks, f, g, fs...) = pullback(C, [f, g, fs...])

pullback(C::WithModel, fs::AbstractVector; context=nothing) = 
  limit(C, Multicospan(fs; cat=getvalue(C)); context)

pullback(C::WithModel, f, g, fs...; context=nothing) = 
  pullback(C, [f, g, fs...]; context)


@model_method pullback_pair

""" Pairing of morphisms: universal property of products/pullbacks.
"""
pullback_pair(C::CatWithPullbacks, lim::AbsLimit, fs::AbstractVector) = 
  pullback_pair[getvalue(C)](lim, fs)

pullback_pair(C::CatWithPullbacks, lim::AbsLimit, f1::T, f2::T) where {T} = 
  pullback_pair(C, lim, [f1, f2])

pullback_pair(m::WithModel, lim::AbsLimit, f1::T, f2::T; context=nothing) where T =
  pullback_pair(m, lim, [f1, f2]; context) 

pullback_pair(m::WithModel, lim::AbsLimit, fs::AbstractVector; context=nothing) = 
  universal(m, lim, Multispan(fs); context)

end # module
