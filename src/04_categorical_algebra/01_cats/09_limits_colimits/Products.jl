module Products
export ThCategoryUnbiasedProducts, CatWithProducts, TypedCatWithProducts, pair

using StructEquality
using GATlab

using .....Theories: codom
import .....Theories: product, universal, pair
import ..FreeDiagrams: ob
using ..Multispans: Multispan
using ..Discrete: DiscreteDiagram
using ..Limits: AbsLimit, ThCategoryLimitBase
import ..Limits: limit

"""
Alternative, unbiased presentation of `ThCategoryWithProducts` which focuses on 
computational and ergonomic aspects at the expense of hiding a lot of structure 
within Julia datatypes such as `DiscreteDiagram`.
"""
@theory ThCategoryUnbiasedProducts <: ThCategoryLimitBase begin
  DiscDiag::TYPE  # type of discrete diagrams, i.e. vectors of Ob

  limit(d::DiscDiag)::Limit
  universal(lim::Limit, d::DiscDiag, sp::MSpan)::(apex(sp) → ob(lim))
end

abstract type WithProducts end 
ThCategoryUnbiasedProducts.Meta.@wrapper CatWithProducts <: WithProducts
ThCategoryUnbiasedProducts.Meta.@typed_wrapper TypedCatWithProducts <: WithProducts

# Boilerplate? Can interconvert between the two. Perhaps `@wrappers Cat TypedCat`
TypedCatWithProducts(c::CatWithProducts) = TypedCatWithProducts(getvalue(c))

CatWithProducts(c::TypedCatWithProducts) = CatWithProducts(getvalue(c))

# Named limits / universal properties
#####################################

""" When product is called on two or more things, we assume they are a list of 
objects to be put into a discrete diagram """
product(m::CatWithProducts, x, y, xs...) = product[getvalue(m)](x,y,xs...)

product(m::WithModel, x, y, xs...; context=nothing) = limit(m, DiscreteDiagram([x,y,xs...]); context)


""" Pairing of morphisms: universal property of products.
"""
  
pair(C::WithProducts, lim::AbsLimit, fs::AbstractVector) = pair[getvalue(C)](lim, fs)

pair(C::WithProducts, lim::AbsLimit, f1::T, f2::T) where {T} = pair(C, lim, [f1, f2])

pair(m::WithModel, lim::AbsLimit, f1::T, f2::T; context=nothing) where T =
 pair(m, lim, [f1, f2]) 

pair(m::WithModel, lim::AbsLimit, fs::AbstractVector; context=nothing) = 
  universal(m, lim, DiscreteDiagram(codom.(fs)), Multispan(fs); context)

end # module
