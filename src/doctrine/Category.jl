using ..GAT

@doc """ Doctrine of *category* (with no extra structure)

**Warning**: We compose functions from left to right, i.e., if f:A→B and g:B→C
then compose(f,g):A→C. Under this convention function are applied on the right,
e.g., if a∈A then af∈B.

We retain the usual meaning of the symbol ∘, i.e., g∘f = compose(f,g).
This usage is too entrenched to overturn, however inconvenient it may be.
""" Category

@signature Category(Ob,Hom) begin
  Ob::TYPE
  Hom(dom::Ob,codom::Ob)::TYPE
  
  id(A::Ob)::Hom(A,A)
  compose(f::Hom(A,B), g::Hom(B,C))::Hom(A,C) <= (A::Ob, B::Ob, C::Ob)

  # Extra syntax
  compose(fs::Vararg{Hom}) = foldl(compose, fs)

  # Unicode syntax
  ∘(f::Hom, g::Hom) = compose(g, f)
  ∘(fs::Vararg{Hom}) = foldl(∘, fs)
end
