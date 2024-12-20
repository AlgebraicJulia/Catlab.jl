module Coproducts
export CoproductColimit, ThCategoryUnbiasedCoproducts, CatWithCoproducts, TypedCatWithCoproducts

using StructEquality
using GATlab

import .....Theories: coproduct, universal
import ..FreeDiagrams: ob
using ..Multispans: Multicospan
using ..Discrete: DiscreteDiagram
using ..Colimits: AbsColimit
import ..Colimits: colimit
using ..Initials: ThCategoryWithInitial

""" Coproducts of a discrete diagram are always represented as Multispans """
@struct_hash_equal struct CoproductColimit <: AbsColimit 
  cocone::Multicospan
end 


"""
Alternative, unbiased presentation of `ThCategoryWithCoproducts` which focuses on 
computational and ergonomic aspects at the expense of hiding a lot of structure 
within Julia datatypes such as `DiscreteDiagram`.
"""
@theory ThCategoryUnbiasedCoproducts <: ThCategoryWithInitial begin
  DiscDiag::TYPE  # type of discrete diagrams, i.e. vectors of Ob
  MCospan::TYPE # type of (multi)cospans
  ap(s::MCospan)::Ob # apex of the span

  Coproduct(d::DiscDiag)::TYPE # Unbiased products.
  coproduct(d::DiscDiag)::Coproduct(d)

  ob(Π::Coproduct(d))::Ob ⊣ [d::DiscDiag]

  # We can't explicit explicitly represent proj functions of a DiscDiag
  universal(Π::Coproduct(d), s::MCospan)::(ap(s) → ob(Π)) ⊣ [d::DiscDiag]
end

ThCategoryUnbiasedCoproducts.Meta.@typed_wrapper TypedCatWithCoproducts
ThCategoryUnbiasedCoproducts.Meta.@wrapper CatWithCoproducts


# Boilerplate? Can interconvert between the two
# Perhaps `@wrappers Cat TypedCat`
TypedCatWithCoproducts(c::CatWithCoproducts) = 
  TypedCatWithCoproducts(getvalue(c))

CatWithCoproducts(c::TypedCatWithCoproducts) = 
  CatWithCoproducts(getvalue(c))

""" When product is called on two or more things, we assume they are a list of 
objects to be put into a discrete diagram """
coproduct(m::CatWithCoproducts, x, y, xs...) =
  coproduct(m, DiscreteDiagram([x,y,xs...]))
  
colimit(m::CatWithCoproducts, d::DiscreteDiagram) = coproduct(m, d)

end # module
