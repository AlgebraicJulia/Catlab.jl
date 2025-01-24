module Pullbacks 
export Pullback, pullback, BinaryEqualizer, ComposeProductEqualizer

import .....Theories: proj1, proj2, pair, ⋅, compose
using ...FreeDiagrams

using ..Limits, ..Products, ..Equalizers
import ..Limits: limit, universal

const BinaryPullback{Ob} = AbstractLimit{Ob,<:Cospan}
const Pullback{Ob} = AbstractLimit{Ob,<:Multicospan}


""" Compute pullback by composing a product with an equalizer.

See also: [`ComposeCoproductCoequalizer`](@ref).
"""
struct ComposeProductEqualizer <: LimitAlgorithm end

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pullback, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback{Ob, Diagram<:Multicospan, Cone<:Multispan{Ob},
    Prod<:Product, Eq<:Equalizer} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  eq::Eq
end

function limit(cospan::Multicospan, ::ComposeProductEqualizer)
  prod = product(feet(cospan))
  (ι,) = eq = equalizer(map(compose, legs(prod), legs(cospan)))
  cone = Multispan(map(π -> ι⋅π, legs(prod)))
  CompositePullback(cospan, cone, prod, eq)
end


""" Pullback of a pair of morphisms with common codomain.

To implement for a type `T`, define the method `limit(::Cospan{T})` and/or
`limit(::Multicospan{T})` or, if you have already implemented products and
equalizers, rely on the default implementation.
"""
pullback(f, g; kw...) = limit(Cospan(f, g); kw...)
pullback(fs::AbstractVector; kw...) = limit(Multicospan(fs); kw...)

function universal(lim::CompositePullback, cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

proj1(lim::BinaryPullback) = first(legs(lim))
proj2(lim::BinaryPullback) = last(legs(lim))

pair(lim::BinaryPullback, f, g) =
  universal(lim, Span(f, g))
pair(lim::Pullback, fs::AbstractVector) =
  universal(lim, Multispan(fs))

end # module
