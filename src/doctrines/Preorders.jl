export Preorder, ThinCategory, MonoidalThinCategory, FreePreorder,
  FreeThinCategory, FreeMononoidalThinCategory,
  Elt, Leq, ≤, reflexive, transitive

""" Doctrine of *Thin category*

Thin categories have at most one Hom between any two objects.
"""
@theory Category(Ob,Hom) => ThinCategory(Ob,Hom) begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeThinCategory(ObExpr,HomExpr) ThinCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

""" Doctrine of *Preorder*

Preorders encode the axioms of reflexivity and transitivity as term constructors.
"""
@theory Preorder(Ob,Leq) begin
  # METATYPES of the GAT
  Ob::TYPE
  Leq(lhs::Ob, rhs::Ob)::TYPE
  @op (≤) := Leq
  # Axioms of the mathematical object are lifted to term constructors in the GAT
  reflexive(A::Ob)::(A≤A) # ∀ A there is a term reflexive(A) which implies A≤A
  transitive(f::(A≤B), g::(B≤C))::(A≤C) ⊣ (A::Ob, B::Ob, C::Ob)

  # axioms of the GAT are equivalences on terms or simplification rules in the logic
  f == g ⊣ (A::Ob, B::Ob, f::(A≤B), g::(A≤B))
  # read as (f⟹ A≤B ∧ g⟹ A≤B) ⟹ f ≡ g
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


@syntax FreePreorder(ObExpr,HomExpr) Preorder begin
  transitive(f::Leq, g::Leq) = associate(new(f,g; strict=true))
end

@theory SymmetricMonoidalCategory(Ob,Hom) => MonoidalThinCategory(Ob,Hom) begin
  f == g ⊣ (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B))
end

@syntax FreeMonoidalThinCategory(ObExpr,HomExpr) MonoidalThinCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
  #otimes(A::Ob, B::Ob) = associate_unit(new(A,B), munit)
  #otimes(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end
