export CategoryWithProducts, ob, hom, terminal, product, proj1, proj2, pair

""" Theory of a *category with (finite) products*

Finite products are presented in biased style, via the nullary case (terminal
objects) and the binary case (binary products). The equational axioms are
standard, especially in type theory (Lambek & Scott, 1986, Section I.3).

For a monoidal category axiomatization, see: [`CartesianCategory`](@ref)
"""
@theory Category(Ob,Hom) => CategoryWithProducts(Ob,Hom,Term,Prod) begin
  Term()::TYPE
  Prod(A::Ob, B::Ob)::TYPE
  
  terminal()::Term()
  product(A::Ob, B::Ob)::Prod(A,B)
  @op (×) := product
  
  ob(⊤::Term())::Ob
  hom(T::Term(), C::Ob)::(C → ob(⊤))
  
  ob(Π::Prod(A,B))::Ob ⊣ (A::Ob, B::Ob)
  proj1(Π::Prod(A,B))::(ob(Π) → A) ⊣ (A::Ob, B::Ob)
  proj2(Π::Prod(A,B))::(ob(Π) → B) ⊣ (A::Ob, B::Ob)
  pair(Π::Prod(A,B), f::(C → A), g::(C → B))::(C → ob(Π)) ⊣ (A::Ob, B::Ob, C::Ob)
  
  # Projection axioms.
  (pair(Π,f,g) ⋅ proj1(Π) == f
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), f::(C → A), g::(C → B)))
  (pair(Π,f,g) ⋅ proj2(Π) == g
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), f::(C → A), g::(C → B)))
  # Uniqueness axioms.
  f == g ⊣ (A::Ob, B::Ob, ⊤::Term(), f::(A → ob(⊤)), g::(B → ob(⊤)))
  (pair(h⋅proj1(Π), h⋅proj2(Π)) == h
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Prod(A,B), h::(C → ob(Π))))
end
