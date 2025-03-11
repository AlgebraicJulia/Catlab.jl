export ThSchema, FreeSchema, AttrType, Attr, SchemaExpr, AttrTypeExpr, AttrExpr, ThPointedSetSchema, FreePointedSetSchema,zeromap

# Schema

########

""" The GAT that parameterizes Attributed C-sets
A schema is comprised of a category C, a discrete category D, and a profunctor
Attr : C^op x D → Set. In GAT form, this is given by extending the theory of
categories with two extra types, AttrType for objects of D, and Attr, for elements
of the sets given by the profunctor.
"""
@theory ThSchema <: ThCategory begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE

  # """ Composition is given by the action of the profunctor on C.
  # """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ [A::Ob, B::Ob, X::AttrType]

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ [A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)])
  compose(id(A), a) == a ⊣ [A::Ob, X::AttrType, a::Attr(A,X)]
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type AttrTypeExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@symbolic_model FreeSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} ThSchema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

@theory ThPointedSetSchema <: ThPointedSetCategory begin
  AttrType::TYPE
  Attr(dom::Ob,codom::AttrType)::TYPE
  zeromap(A::Ob,X::AttrType)::Attr(A,X)

  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ [A::Ob, B::Ob, X::AttrType]

  compose(f,zeromap(B,X)) == zeromap(A,X) ⊣ [A::Ob, B::Ob, X::AttrType, f::Hom(A,B)]
  compose(zeromap(A,B),f) == zeromap(A,X) ⊣ [A::Ob, B::Ob, X::AttrType, f::Attr(B,X)]

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ [A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)])
  compose(id(A), a) == a ⊣ [A::Ob, X::AttrType, a::Attr(A,X)]
end

@symbolic_model FreePointedSetSchema{ObExpr,HomExpr,AttrTypeExpr,AttrExpr} ThPointedSetSchema begin
  compose(f::Hom,g::Hom) = associate_unit(normalize_zero(new(f,g; strict=true)), id)
  compose(f::Hom,a::Attr) = associate_unit(normalize_zero(new(f,a; strict=true)), id)
end


@theory ThDoubleSchema <: ThDoubleCategory begin
    AttrType::TYPE
    Attr(dom::Ob,codom::AttrType)::TYPE

    # """ Composition is given by the action of the profunctor on C.
    # """
    compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ [A::Ob, B::Ob, X::AttrType]

    (compose(f, compose(g, a)) == compose(compose(f, g), a)
        ⊣ [A::Ob, B::Ob, C::Ob, X::AttrType, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)])
    compose(id(A), a) == a ⊣ [A::Ob, X::AttrType, a::Attr(A,X)]
end

""" Syntax for a double category with "attr types".

Doesn't check for 
"""
@symbolic_model FreeDoubleSchema{ObExpr,HomExpr,ProExpr,CellExpr,AttrTypeExpr, AttrExpr} ThDoubleSchema begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(α::Cell, β::Cell) = associate_unit(new(α,β), id)
  pcompose(m::Pro, n::Pro) = associate_unit(new(m,n; strict=true), pid)
  pcompose(α::Cell, β::Cell) = associate_unit(new(α,β), pid)
  compose(f::Hom,g::Hom) = associate_unit(normalize_zero(new(f,g; strict=true)), id)
  compose(f::Hom,a::Attr) = associate_unit(normalize_zero(new(f,a; strict=true)), id)
end

export ThDoubleSchema, FreeDoubleSchema
