using ..GAT
using ..Syntax

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
  ∘(f::Hom, g::Hom) = compose(g, f)
  ∘(fs::Vararg{Hom}) = foldl(∘, fs)
end

@syntax FreeCategory Category begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
end

@doc """ Doctrine of (strict) *2-category*
""" Category2

@signature Category(Ob,Hom) => Category2(Ob,Hom,Hom2) begin
  Hom2(dom::Hom(A,B), codom::Hom(A,B))::TYPE <= (A::Ob, B::Ob)
  
  # Hom categories: Vertical composition
  id(f)::Hom2(f,f) <= (A::Ob, B::Ob, f::Hom(A,B))
  compose(α::Hom2(f,g), β::Hom2(g,h))::Hom2(f,h) <=
    (A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B), h::Hom(A,B))
  
  # Horizontal compostion
  compose2(α::Hom2(f,g), β::Hom2(h,k))::Hom2(compose(f,h),compose(g,k)) <=
    (A::Ob, B::Ob, C::Ob, f::Hom(A,B), g::Hom(A,B), h::Hom(B,C), k::Hom(B,C))
  
  # Extra syntax
  compose(αs::Vararg{Hom2}) = foldl(compose, αs)
  compose2(αs::Vararg{Hom2}) = foldl(compose2, αs)
  ∘(α::Hom2, β::Hom2) = compose(g, f)
  ∘(αs::Vararg{Hom2}) = foldl(∘, αs)
end

@doc """ Syntax for a 2-category.

Checks domains of morphisms but not 2-morphisms.
""" FreeCategory2

@syntax FreeCategory2 Category2 begin
  compose(f::Hom, g::Hom) = associate(Super.compose(f,g; strict=true))
  compose(α::Hom2, β::Hom2) = associate(Super.compose(α,β))
  compose2(α::Hom2, β::Hom2) = associate(Super.compose2(α,β))
end
