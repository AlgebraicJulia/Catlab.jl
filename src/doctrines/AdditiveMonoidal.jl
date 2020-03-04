export AdditiveMonoidalCategory, oplus, ⊕, ozero,
  AdditiveSymmetricMonoidalCategory, FreeAdditiveSymmetricMonoidalCategory

# Monoidal category
###################

""" Doctrine of *monoidal category* in additive notation

The same as `MonoidalCategory` mathematically but with different notation.
"""
@signature Category(Ob,Hom) => AdditiveMonoidalCategory(Ob,Hom) begin
  oplus(A::Ob, B::Ob)::Ob
  oplus(f::Hom(A,B), g::Hom(C,D))::Hom(oplus(A,C),oplus(B,D)) <=
    (A::Ob, B::Ob, C::Ob, D::Ob)
  ozero()::Ob
  
  # Unicode syntax
  ⊕(A::Ob, B::Ob) = oplus(A, B)
  ⊕(f::Hom, g::Hom) = oplus(f, g)
end

# Convenience constructors
oplus(xs::Vector{T}) where T = isempty(xs) ? ozero(T) : foldl(oplus, xs)
oplus(x, y, z, xs...) = oplus([x, y, z, xs...])

# Symmetric monoidal category
#############################

""" Doctrine of *symmetric monoidal category* in additive notation

The same as `SymmetricMonoidalCategory` mathematically but with different
notation.
"""
@signature AdditiveMonoidalCategory(Ob,Hom) => AdditiveSymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::Hom(oplus(A,B),oplus(B,A))
end

@syntax FreeAdditiveSymmetricMonoidalCategory(ObExpr,HomExpr) AdditiveSymmetricMonoidalCategory begin
  oplus(A::Ob, B::Ob) = associate_unit(new(A,B), ozero)
  oplus(f::Hom, g::Hom) = associate(new(f,g))
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end
