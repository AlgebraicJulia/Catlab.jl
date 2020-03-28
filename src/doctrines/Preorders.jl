export Preorder, ThinCategory, MonoidalThinCategory, FreePreorder,
  FreeThinCategory, FreeMonoidalThinCategory,
  Elt, Leq, ≤, lhs, rhs, reflexive, transitive

""" Doctrine of *thin category*

Thin categories have at most one morphism between any two objects.
"""
@theory Category(Ob,Hom) => ThinCategory(Ob,Hom) begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinCategory(ObExpr,HomExpr) ThinCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

""" Doctrine of *preorder*

Preorders encode the axioms of reflexivity and transitivity as term constructors.
"""
@theory Preorder(Elt,Leq) begin
  Elt::TYPE
  Leq(lhs::Elt, rhs::Elt)::TYPE
  @op (≤) := Leq

  # Preorder axioms are lifted to term constructors in the GAT.
  reflexive(A::Elt)::(A≤A) # ∀ A there is a term reflexive(A) which implies A≤A
  transitive(f::(A≤B), g::(B≤C))::(A≤C) ⊣ (A::Elt, B::Elt, C::Elt)

  # Axioms of the GAT are equivalences on terms or simplification rules in the logic
  f == g ⊣ (A::Elt, B::Elt, f::(A≤B), g::(A≤B))
  # Read as (f⟹ A≤B ∧ g⟹ A≤B) ⟹ f ≡ g
end

@syntax FreePreorder(ObExpr,HomExpr) Preorder begin
  transitive(f::Leq, g::Leq) = associate(new(f,g; strict=true))
end

# a GAT-homomorphism between the Preorder GAT and the ThinCategory GAT
# this is a morphism is *Gat* the category whose objects are doctrines
# and whose morphisms are algebraic structure preserving maps

# @functor F(Preorder(Ob, Leq))::ThinCategory(Ob, Hom) begin
#   Ob ↦ Ob
#   Leq ↦ Hom
#   reflexive ↦ id
#   transitive ↦ compose
# end

@theory SymmetricMonoidalCategory(Ob,Hom) => MonoidalThinCategory(Ob,Hom) begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeMonoidalThinCategory(ObExpr,HomExpr) MonoidalThinCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  #otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  #otimes(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end
