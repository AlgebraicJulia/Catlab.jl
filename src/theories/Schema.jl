export ThSchema, FreeSchema, AttrType, Attr, SchemaExpr, AttrTypeExpr, AttrExpr,
  ThPtSchema, FreePtSchema, ZeroAttr, ZeroAttrExpr, ZAtt,z,attr

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

@theory ThPtSchema{Ob,Hom,ZeroHom,AttrType,Attr,ZeroAttr} <: ThPtCategory{Ob,Hom,ZeroHom} begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE
  ZeroAttr(dom::Ob,codom::AttrType)::TYPE

  ZAtt()::AttrType
  z(A::Ob,X::AttrType)::ZeroAttr(A,X)
  attr(x::ZeroAttr(A,X))::Attr(A,X)⊣(A::Ob,X::AttrType)

  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)
  compose(f::Hom(A,B),x::ZeroAttr(B,X))::ZeroAttr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)
  compose(x::ZeroHom(A,B),a::Attr(B,X))::ZeroAttr(A,X) ⊣ (A::Ob, B::Ob, X::AttrType)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::AttrType, a::Attr(A,X))
  x₁==x₂⊣(A::Ob,X::AttrType,x₁::ZeroAttr(A,X),x₂::ZeroAttr(A,X))
end

abstract type ZeroAttrExpr{T} <: SchemaExpr{T} end

@syntax FreePtSchema{ObExpr,HomExpr,ZeroHomExpr,AttrTypeExpr,AttrExpr,ZeroAttrExpr} ThPtSchema begin
  compose(f::Hom,g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom,x::ZeroHom) = z(dom(f),codom(x))
  compose(x::ZeroHom,g::Hom) = z(dom(x),codom(g))
  compose(f::Hom,x::ZeroAttr) = z(dom(f),codom(x))
  compose(x::ZeroHom,a::Attr) = z(dom(x),codom(a))
end