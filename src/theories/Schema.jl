export Schema, FreeSchema, AttrType, Attr,
  SchemaExpr, AttrTypeExpr, AttrExpr, parse_schema

using MLStyle: @match
using ...Meta: strip_lines

# Schema
########

""" The GAT that parameterizes Attributed C-sets
A schema is comprised of a category C, a discrete category D, and a profunctor
Attr : C^op x D → Set. In GAT form, this is given by extending the theory of
categories with two extra types, AttrType for objects of D, and Attr, for elements
of the sets given by the profunctor.
"""
@theory Schema{Ob,Hom,AttrType,Attr} <: Category{Ob,Hom} begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE

  """ Composition is given by the action of the profunctor on C.
  """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::AttrType, a::Attr(A,X))
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type AttrTypeExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@syntax FreeSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} Schema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

# Type-level representation of Schema
#####################################

function intify(tuple,s)
  findfirst(tuple .== s)
end

function tuplize(xs,f)
  (;[nameof(x) => nameof(f(x)) for x in xs]...)
end

struct SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}
end

const ACSetSchemaDescType = SchemaDescType
const CSetSchemaDescType{obs,homs,doms,codoms} = SchemaDescType{obs,homs,(),(),doms,codoms}

function SchemaDescTypeType(p::Presentation)
  obs,homs,attrtypes,attrs = map(t -> p.generators[t],[:Ob,:Hom,:AttrType,:Attr])
  ob_syms,hom_syms,attrtype_syms,attr_syms = map(xs -> Tuple(nameof.(xs)),
                                                 [obs,homs,attrtypes,attrs])
  homdoms = map(t -> intify(ob_syms,t),tuplize(homs,dom))
  homcodoms = map(t -> intify(ob_syms,t),tuplize(homs,codom))
  attrdoms = map(t -> intify(ob_syms,t),tuplize(attrs,dom))
  attrcodoms = map(t -> intify(attrtype_syms,t),tuplize(attrs,codom))
  SchemaDescType{
    ob_syms,
    hom_syms,
    attrtype_syms,
    attr_syms,
    (;homdoms...,attrdoms...),
    (;homcodoms...,attrcodoms...)
  }
end

ob(::Type{<:SchemaDescType{obs}}) where {obs} = obs
hom(::Type{<:SchemaDescType{obs,homs}}) where {obs,homs} = homs

function dom_nums(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  Tuple(map(last, filter(((f,_),) -> f ∈ homs, collect(pairs(doms)))))
end

dom(T::Type{<:SchemaDescType}) = map(i -> ob(T)[i], dom_nums(T))
function dom_num(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}},f::Symbol) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  doms[f]
end
dom(T::Type{<:SchemaDescType},f::Symbol) = ob(T)[dom_num(T,f)]

function codom_nums(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  Tuple(map(last, filter(((f,_),) -> f ∈ homs, collect(pairs(codoms)))))
end

codom(T::Type{<:SchemaDescType}) = map(i -> ob(T)[i], codom_nums(T))
function codom_num(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}},f::Symbol) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  codoms[f]
end
codom(T::Type{<:SchemaDescType},f::Symbol) = ob(T)[codom_num(T,f)]

attr(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms} = attrs
attrtype(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms} = attrtypes

function adom_nums(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  Tuple(map(last, filter(((f,_),) -> f ∈ attrs, collect(pairs(doms)))))
end

adom(T::Type{<:SchemaDescType}) = map(i -> ob(T)[i], adom_nums(T))

function acodom_nums(::Type{<:SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
  {obs,homs,attrtypes,attrs,doms,codoms}
  Tuple(map(last, filter(((f,_),) -> f ∈ attrs, collect(pairs(codoms)))))
end

acodom(T::Type{<:SchemaDescType}) = map(i -> attrtype(T)[i], acodom_nums(T))

struct SchemaDesc
  obs::Vector{Symbol}
  homs::Vector{Symbol}
  attrtypes::Vector{Symbol}
  attrs::Vector{Symbol}
  doms::Dict{Symbol,Symbol}
  codoms::Dict{Symbol,Symbol}
  function SchemaDesc(::Type{SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}}) where
      {obs,homs,attrtypes,attrs,doms,codoms}
    homdoms = [f => obs[doms[f]] for f in homs]
    homcodoms = [f => obs[codoms[f]] for f in homs]
    attrdoms = [a => obs[doms[a]] for a in attrs]
    attrcodoms = [a => attrtypes[codoms[a]] for a in attrs]
    new(
      Symbol[obs...],
      Symbol[homs...],
      Symbol[attrtypes...],
      Symbol[attrs...],
      Dict{Symbol,Symbol}(homdoms...,attrdoms...),
      Dict{Symbol,Symbol}(homcodoms...,attrcodoms...)
    )
  end
end
