module Products 
export BinaryProduct, Product, product, proj1, proj2, pair

import .....Theories: proj1, proj2, product, pair
using ...FreeDiagrams

using ..Limits

const BinaryProduct{Ob} = AbstractLimit{Ob,<:ObjectPair}
const Product{Ob} = AbstractLimit{Ob,<:DiscreteDiagram}


""" Product of objects.

To implement for a type `T`, define the method `limit(::ObjectPair{T})` and/or
`limit(::DiscreteDiagram{T})`.
"""
product(A, B; kw...) = limit(ObjectPair(A, B); kw...)
product(As::AbstractVector; kw...) = limit(DiscreteDiagram(As); kw...)



proj1(lim::BinaryProduct) = first(legs(lim))
proj2(lim::BinaryProduct) = last(legs(lim))


""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(f, g) = pair(product(codom(f), codom(g)), f, g)

pair(fs::AbstractVector) = pair(product(map(codom, fs)), fs)

pair(lim::BinaryProduct, f, g) = universal(lim, Span(f, g))

pair(lim::Product, fs::AbstractVector) = universal(lim, Multispan(fs))

end # module
