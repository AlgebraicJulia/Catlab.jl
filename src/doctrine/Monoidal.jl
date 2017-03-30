using ..GAT

@doc """ Doctrine of *monoidal category*

To avoid associators and unitors, we assume the monoidal category is *strict*.
By the coherence theorem there is no loss of generality, but we may add a
typeclass for weak monoidal categories later.
""" MonoidalCategory

@signature Category(Ob,Hom) => MonoidalCategory(Ob,Hom) begin
  otimes(A::Ob, B::Ob)::Ob
  otimes(f::Hom(A,B), g::Hom(C,D))::Hom(otimes(A,C),otimes(B,D))
  munit()::Ob

  # Extra syntax
  otimes(As::Vararg{Ob}) = foldl(otimes, As)
  otimes(fs::Vararg{Hom}) = foldl(otimes, fs)

  # Unicode syntax
  ⊗(A::Ob, B::Ob) = otimes(A, B)
  ⊗(f::Hom, g::Hom) = otimes(f, g)
  ⊗(As::Vararg{Ob}) = otimes(As...)
  ⊗(fs::Vararg{Hom}) = otimes(fs...)
end

@doc """ Doctrine of *symmetric monoidal category*

In fact, the signature (but not the axioms) is the same as a braided monoidal
category.
""" SymmetricMonoidalCategory

@signature MonoidalCategory(Ob,Hom) => SymmetricMonoidalCategory(Ob,Hom) begin
  braid(A::Ob, B::Ob)::Hom(otimes(A,B),otimes(B,A))
  
  # Unicode syntax
  σ(A::Ob, B::Ob) = braid(A, B)
end

@doc """ Doctrine of *compact closed category*
""" CompactClosedCategory

@signature SymmetricMonoidalCategory(Ob,Hom) => CompactClosedCategory(Ob,Hom) begin
  dual(A::Ob)::Ob
  
  ev(A::Ob)::Hom(otimes(A,dual(A)), munit())
  coev(A::Ob)::Hom(munit(), otimes(dual(A),A))
end

@doc """ Doctrine of *dagger category*
""" DaggerCategory

@signature Category(Ob,Hom) => DaggerCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end

@doc """ Doctrine of *dagger compact category*

FIXME: This signature should extend both `DaggerCategory` and
`CompactClosedCategory`, but we don't support multiple inheritance yet.
""" DaggerCompactCategory

@signature CompactClosedCategory(Ob,Hom) => DaggerCompactCategory(Ob,Hom) begin
  dagger(f::Hom(A,B))::Hom(B,A) <= (A::Ob,B::Ob)
end
