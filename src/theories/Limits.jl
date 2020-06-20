export CategoryWithProducts, ob, terminal, delete, product, proj1, proj2, pair,
  CategoryWithCoproducts, initial, create, coproduct, coproj1, coproj2, copair,
  CompleteCategory, equalizer, incl, factorize

# Limits
########

""" Theory of a *category with (finite) products*

Finite products are presented in biased style, via the nullary case (terminal
objects) and the binary case (binary products). The equational axioms are
standard, especially in type theory (Lambek & Scott, 1986, Section 0.5 or
Section I.3).

For a monoidal category axiomatization, see [`CartesianCategory`](@ref).
"""
@theory Category(Ob,Hom) => CategoryWithProducts(Ob,Hom,Terminal,Product) begin
  Terminal()::TYPE
  terminal()::Terminal()
  
  Product(foot1::Ob, foot2::Ob)::TYPE
  product(A::Ob, B::Ob)::Product(A,B)
  #@op (×) := product
  
  ob(⊤::Terminal())::Ob
  delete(⊤::Terminal(), C::Ob)::(C → ob(⊤))
  
  ob(Π::Product(A,B))::Ob ⊣ (A::Ob, B::Ob)
  proj1(Π::Product(A,B))::(ob(Π) → A) ⊣ (A::Ob, B::Ob)
  proj2(Π::Product(A,B))::(ob(Π) → B) ⊣ (A::Ob, B::Ob)
  (pair(Π::Product(A,B), f::(C → A), g::(C → B))::(C → ob(Π))
    ⊣ (A::Ob, B::Ob, C::Ob))
  
  # Projection axioms.
  (pair(Π,f,g) ⋅ proj1(Π) == f
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Product(A,B), f::(C → A), g::(C → B)))
  (pair(Π,f,g) ⋅ proj2(Π) == g
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Product(A,B), f::(C → A), g::(C → B)))
  
  # Uniqueness axioms.
  f == g ⊣ (C::Ob, ⊤::Terminal(), f::(C → ob(⊤)), g::(C → ob(⊤)))
  (pair(h⋅proj1(Π), h⋅proj2(Π)) == h
    ⊣ (A::Ob, B::Ob, C::Ob, Π::Product(A,B), h::(C → ob(Π))))
end

""" Theory of a *(finitely) complete category*

Finite limits are presented in biased style, via finite products and equalizers.
The equational axioms for equalizers are obscure, but can found in (Lambek &
Scott, 1986, Section 0.5), apparently following "Burroni's pioneering ideas".
"""
@theory CategoryWithProducts(Ob,Hom,Terminal,Product) =>
    CompleteCategory(Ob,Hom,Terminal,Product,Equalizer) begin
  Equalizer(f::(A → B), g::(A → B))::TYPE ⊣ (A::Ob, B::Ob)
  equalizer(f::(A → B), g::(A → B))::Equalizer(f,g) ⊣ (A::Ob, B::Ob)
  
  ob(eq::Equalizer(f,g))::Ob ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B))
  incl(eq::Equalizer(f,g))::(ob(eq) → A) ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B))
  (factorize(eq::Equalizer(f,g), h::(C → A),
             eq_h::Equalizer(h⋅f,h⋅g))::(ob(eq_h) → ob(eq))
    ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B)))
  
  (incl(eq)⋅f == incl(eq)⋅g
    ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B), eq::Equalizer(f,g)))
  (incl(eq) == id(A)
    ⊣ (A::Ob, B::Ob, f::(A → B), eq::Equalizer(f,f)))
  (factorize(eq,h,eq_h) ⋅ incl(eq) == incl(eq_h) ⋅ h
    ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B), h::(C → A),
       eq::Equalizer(f,g), eq_h::Equalizer(h⋅f, h⋅g)))
  (factorize(eq, k⋅incl(eq), eq_k) == k
    ⊣ (A::Ob, B::Ob, D::Ob, f::(A → B), g::(A → B), eq::Equalizer(f,g),
       k::(D → ob(eq)), eq_k::Equalizer(k⋅incl(eq)⋅f, k⋅incl(eq)⋅g)))
end

# Colimits
##########

""" Theory of a *category with (finite) coproducts*

Finite coproducts are presented in biased style, via the nullary case (initial
objects) and the binary case (binary coproducts). The axioms are dual to those
of [`CategoryWithProducts`](@ref).

For a monoidal category axiomatization, see [`CocartesianCategory`](@ref).
"""
@theory Category(Ob,Hom) => CategoryWithCoproducts(Ob,Hom,Initial,Coproduct) begin
  Initial()::TYPE
  initial()::Initial()
  
  Coproduct(foot1::Ob, foot2::Ob)::TYPE
  coproduct(A::Ob, B::Ob)::Coproduct(A,B)
  #@op (⊔) := coproduct
  
  ob(⊥::Initial())::Ob
  create(⊥::Initial(), C::Ob)::(ob(⊥) → C)
  
  ob(⨆::Coproduct(A,B))::Ob ⊣ (A::Ob, B::Ob)
  coproj1(⨆::Coproduct(A,B))::(A → ob(⨆)) ⊣ (A::Ob, B::Ob)
  coproj2(⨆::Coproduct(A,B))::(B → ob(⨆)) ⊣ (A::Ob, B::Ob)
  (copair(⨆::Coproduct(A,B), f::(A → C), g::(B → C))::(ob(⨆) → C)
    ⊣ (A::Ob, B::Ob, C::Ob))
  
  # Coprojection axioms.
  (coproj1(⨆) ⋅ copair(⨆,f,g) == f
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coproduct(A,B), f::(A → C), g::(B → C)))
  (coproj2(⨆) ⋅ copair(⨆,f,g) == g
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coproduct(A,B), f::(A → C), g::(B → C)))
  
  # Uniqueness axioms.
  f == g ⊣ (C::Ob, ⊥::Initial(), f::(ob(⊥) → C), g::(ob(⊥) → C))
  (copair(coproj1(⨆)⋅h, coproj2(⨆)⋅h) == h
    ⊣ (A::Ob, B::Ob, C::Ob, ⨆::Coproduct(A,B), h::(ob(⨆) → C)))
end
