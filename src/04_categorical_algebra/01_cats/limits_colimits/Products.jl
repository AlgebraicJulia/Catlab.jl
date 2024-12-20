module Products
export ProductLimit, ThCategoryUnbiasedProducts, CatWithProducts, TypedCatWithProducts

using StructEquality
using GATlab

import .....Theories: product, universal
import ..FreeDiagrams: ob
using ..Multispans: Multispan
using ..Discrete: DiscreteDiagram
using ..Limits: AbsLimit
import ..Limits: limit
using ..Terminals: ThCategoryWithTerminal

""" Products of a discrete diagram are always represented as Multispans """
@struct_hash_equal struct ProductLimit <: AbsLimit 
  cone::Multispan
end 


"""
Alternative, unbiased presentation of `ThCategoryWithProducts` which focuses on 
computational and ergonomic aspects at the expense of hiding a lot of structure 
within Julia datatypes such as `DiscreteDiagram`.
"""
@theory ThCategoryUnbiasedProducts <: ThCategoryWithTerminal begin
  DiscDiag::TYPE  # type of discrete diagrams, i.e. vectors of Ob
  MSpan::TYPE # type of (multi)spans
  ap(s::MSpan)::Ob # apex of the span

  Product(d::DiscDiag)::TYPE # Unbiased products.
  product(d::DiscDiag)::Product(d)

  ob(Π::Product(d))::Ob ⊣ [d::DiscDiag]

  # We can't explicit explicitly represent proj functions of a DiscDiag
  universal(Π::Product(d), s::MSpan)::(ap(s) → ob(Π)) ⊣ [d::DiscDiag]
end

ThCategoryUnbiasedProducts.Meta.@wrapper CatWithProducts
ThCategoryUnbiasedProducts.Meta.@typed_wrapper TypedCatWithProducts

# Boilerplate? Can interconvert between the two. Perhaps `@wrappers Cat TypedCat`
TypedCatWithProducts(c::CatWithProducts) = TypedCatWithProducts(getvalue(c))

CatWithProducts(c::TypedCatWithProducts) = CatWithProducts(getvalue(c))

""" When product is called on two or more things, we assume they are a list of 
objects to be put into a discrete diagram """
product(m::CatWithProducts, x, y, xs...) = product(m, DiscreteDiagram([x,y,xs...]))

limit(m::CatWithProducts, d::DiscreteDiagram) = product(m, d)
  
end # module
