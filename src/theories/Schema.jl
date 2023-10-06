export ThSchema, FreeSchema, AttrType, Attr, SchemaExpr, AttrTypeExpr, AttrExpr, ThPointedSchema, FreePointedSchema,zeromap, ZeroAttr

# Schema

########

""" The GAT that parameterizes Attributed C-sets
A schema is comprised of a category C, a discrete category D, and a profunctor
Attr : C^op x D → Set. In GAT form, this is given by extending the theory of
categories with two extra types, AttrType for objects of D, and Attr, for elements
of the sets given by the profunctor.
"""
@theory ThSchema{Ob,Hom,AttrType,Attr} <: ThCategory{Ob,Hom} begin
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

@syntax FreeSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} ThSchema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

"""
A pointed schema is a schema which is pointed on both sides.
"""
@theory ThPointedSchema{Ob,Hom,AttrType,Attr} <: ThPointedCategory{Ob,Hom} begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE

  ZeroAttr()::AttrType
  zeromap(A::Ob,X::AttrType)::Attr(A,X)

  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  compose(f::Hom(A,B),zeromap(B,X)) == zeromap(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)
  compose(zeromap(A,B),f::Hom(B,X)) == zeromap(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::AttrType, a::Attr(A,X))
  #a == b ⊣(A::Ob,a::Attr(A,ZeroAttr()),b::Attr(A,ZeroAttr()))
end

@syntax FreePointedSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} ThPointedSchema begin
  compose(f::Hom,g::Hom) = associate_unit(normalize_zero(new(f,g; strict=true)), id)
  compose(f::Hom,a::Attr) = associate_unit(normalize_zero(new(f,a; strict=true)), id)
end