module Pullbacks
export AbsPullbackLimit, CompositePullback, NestedLoopJoin, SortMergeJoin, HashJoin, SmartJoin

using StructEquality
using GATlab

using ...Categories: Category
using ...FreeDiagrams: Multispan, Multicospan

using ..Limits: AbsLimit, JoinAlgorithm, ComposeProductEqualizer
using ..Products: ProductLimit
using ..Equalizers: EqLimit

""" Unlike other limits, there are many different ways to represent a Pullback 
in Catlab """ 
abstract type AbsPullbackLimit <: AbsLimit end 


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


# Composite pullback
#-------------------

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pullback, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback <: AbsLimit
  cone::Multispan
  prod::ProductLimit
  eq::EqLimit
end


"""
`CompositePullback` is constructed via applying the `ComposeProductEqualizer` 
algorithm to a cospan.
"""
function limit(cospan::Multicospan, m::Category, ::ComposeProductEqualizer)
  prod = product(feet(cospan), m)
  (ι,) = eq = equalizer(map(compose[getvalue(m)], legs(prod), legs(cospan)), m)
  cone = Multispan(map(π -> compose[getvalue(m)](ι,π), legs(prod)))
  Limit(Diagram(cospan, m), CompositePullback(cone, prod, eq))
end

function _universal(::Multicospan, ::Category, lim::CompositePullback, 
                    cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

pullback(fs::AbstractVector, model::Category; alg=DefaultLimit()) = 
  limit(Multicospan(fs), model, alg)

pullback(f, g, model::Category; alg=DefaultLimit()) = 
  limit(Multicospan([f,g]), model, alg)

end # module
