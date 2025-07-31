module Coproducts
export ThCategoryUnbiasedCoproducts, CatWithCoproducts, TypedCatWithCoproducts, coproduct, copair

using StructEquality
using GATlab

using .....Theories: dom
import .....Theories: coproduct, universal, copair
using ..FreeDiagrams: Multicospan, apex, DiscreteDiagram
import ..FreeDiagrams: ob
using ..Colimits: AbsColimit, ThCategoryColimitBase
import ..Colimits: colimit, cocone

"""
Alternative, unbiased presentation of `ThCategoryWithCoproducts` which focuses on 
computational and ergonomic aspects at the expense of hiding a lot of structure 
within Julia datatypes such as `DiscreteDiagram`.
"""
@theory ThCategoryUnbiasedCoproducts <: ThCategoryColimitBase begin
  DiscDiag::TYPE{DiscreteDiagram}  # type of discrete diagrams, i.e. vectors of Ob

  colimit(d::DiscDiag)::Colimit # Unbiased products.

  # We can't explicit explicitly represent proj functions of a DiscDiag
  universal(Σ::Colimit, d::DiscDiag, csp::MCospan)::(ob(Σ) → apex(csp))
end

abstract type WithCoproducts end
ThCategoryUnbiasedCoproducts.Meta.@typed_wrapper TypedCatWithCoproducts <: WithCoproducts
ThCategoryUnbiasedCoproducts.Meta.@wrapper CatWithCoproducts <: WithCoproducts


# Boilerplate? Can interconvert between the two
# Perhaps `@wrappers Cat TypedCat`
TypedCatWithCoproducts(c::CatWithCoproducts) = 
  TypedCatWithCoproducts(getvalue(c))

CatWithCoproducts(c::TypedCatWithCoproducts) = 
  CatWithCoproducts(getvalue(c))

# Named limits / universal properties
#####################################
@model_method coproduct

""" When product is called on two or more things, we assume they are a list of 
objects to be put into a discrete diagram """
coproduct(m::WithCoproducts, x, y, xs...) = 
  coproduct[getvalue(m)](x,y,xs...)

coproduct(m::WithModel, x, xs...; context=nothing) = 
  colimit(m, DiscreteDiagram([x,xs...]); context)

@model_method copair

""" Copairing of morphisms: universal property of coproducts
"""
copair(m::WithModel, colim::AbsColimit, fs::AbstractVector; context=nothing)  =
  universal(m, colim, DiscreteDiagram(dom.(fs)), Multicospan(fs); context)

copair(m::WithModel, colim::AbsColimit, f1::T, f2::T; context=nothing) where T =
  copair(m, colim, [f1,f2]; context)

copair(C::WithCoproducts, colim::AbsColimit, fs::AbstractVector)  =
  copair[getvalue(C)](colim, fs)

copair(C::WithCoproducts, lim::AbsColimit, f1::T,f2::T) where {T} = 
  copair(C, lim, [f1, f2])

end # module
