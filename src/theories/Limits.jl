export ThCategoryWithProducts, ob, terminal, delete, product, proj1, proj2, pair,
  ThCategoryWithCoproducts, initial, create, coproduct, coproj1, coproj2, copair,
  ThCompleteCategory, equalizer, incl, factorize,
  ThCocompleteCategory, coequalizer, proj

# Limits
########

""" Theory of a *category with (finite) products*

Finite products are presented in biased style, via the nullary case (terminal
objects) and the binary case (binary products). The equational axioms are
standard, especially in type theory (Lambek & Scott, 1986, Section 0.5 or
Section I.3). Strictly speaking, this theory is not of a "category with finite
products" (a category in which finite products exist) but of a "category with
*chosen* finite products".

For a monoidal category axiomatization of finite products, see
[`ThCartesianCategory`](@ref).
"""
@theory ThCategoryWithProducts{Ob,Hom,Terminal,Product} <: ThCategory{Ob,Hom} begin
  Terminal()::TYPE
  Product(foot1::Ob, foot2::Ob)::TYPE
  
  # Terminal object.
  terminal()::Terminal()
  ob(⊤::Terminal())::Ob
  delete(⊤::Terminal(), C::Ob)::(C → ob(⊤))
  
  # Binary products.
  product(A::Ob, B::Ob)::Product(A,B)
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
Scott, 1986, Section 0.5), who in turn attribute them to "Burroni's pioneering
ideas". Strictly speaking, this theory is not of a "finitely complete category"
(a category in which finite limits exist) but of a "category with *chosen*
finite limits".
"""
@theory ThCompleteCategory{Ob,Hom,Terminal,Product,Equalizer} <:
    ThCategoryWithProducts{Ob,Hom,Terminal,Product} begin
  Equalizer(f::(A → B), g::(A → B))::TYPE ⊣ (A::Ob, B::Ob)
  
  # Equalizers.
  equalizer(f::(A → B), g::(A → B))::Equalizer(f,g) ⊣ (A::Ob, B::Ob)
  ob(eq::Equalizer(f,g))::Ob ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B))
  (incl(eq::Equalizer(f,g))::(ob(eq) → A)
    ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B)))
  (factorize(eq::Equalizer(f,g), h::(C → A),
             eq_h::Equalizer(h⋅f,h⋅g))::(ob(eq_h) → ob(eq))
    ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B)))
  
  # Equalizer axioms.
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
of [`ThCategoryWithProducts`](@ref).

For a monoidal category axiomatization of finite coproducts, see
[`ThCocartesianCategory`](@ref).
"""
@theory ThCategoryWithCoproducts{Ob,Hom,Initial,Coproduct} <: ThCategory{Ob,Hom} begin
  Initial()::TYPE
  Coproduct(foot1::Ob, foot2::Ob)::TYPE

  # Initial object.
  initial()::Initial()
  ob(⊥::Initial())::Ob
  create(⊥::Initial(), C::Ob)::(ob(⊥) → C)
  
  # Binary coproducts.
  coproduct(A::Ob, B::Ob)::Coproduct(A,B)
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

""" Theory of a *(finitely) cocomplete category*

Finite colimits are presented in biased style, via finite coproducts and
coequalizers. The axioms are dual to those of [`ThCompleteCategory`](@ref).
"""
@theory ThCocompleteCategory{Ob,Hom,Initial,Coproduct,Coequalizer} <:
    ThCategoryWithCoproducts{Ob,Hom,Initial,Coproduct} begin
  Coequalizer(f::(A → B), g::(A → B))::TYPE ⊣ (A::Ob, B::Ob)
  
  # Coequalizers.
  coequalizer(f::(A → B), g::(A → B))::Coequalizer(f,g) ⊣ (A::Ob, B::Ob)
  ob(eq::Coequalizer(f,g))::Ob ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B))
  (proj(eq::Coequalizer(f,g))::(B → ob(eq))
    ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B)))
  (factorize(coeq::Coequalizer(f,g), h::(B → C),
             coeq_h::Coequalizer(f⋅h,g⋅h))::(ob(coeq) → ob(coeq_h))
    ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B)))
  
  # Coequalizer axioms.
  (f⋅proj(coeq) == g⋅proj(coeq)
    ⊣ (A::Ob, B::Ob, f::(A → B), g::(A → B), coeq::Coequalizer(f,g)))
  (proj(coeq) == id(B)
    ⊣ (A::Ob, B::Ob, f::(A → B), coeq::Coequalizer(f,f)))
  (proj(coeq) ⋅ factorize(coeq,h,coeq_h) == h ⋅ proj(coeq_h)
    ⊣ (A::Ob, B::Ob, C::Ob, f::(A → B), g::(A → B), h::(B → C),
       coeq::Coequalizer(f,g), coeq_h::Coequalizer(f⋅h, g⋅h)))
  (factorize(coeq, proj(coeq)⋅k, coeq_k) == k
    ⊣ (A::Ob, B::Ob, D::Ob, f::(A → B), g::(A → B),
       coeq::Coequalizer(f,g), k::(ob(coeq) → D),
       coeq_k::Coequalizer(f⋅proj(coeq)⋅k, g⋅proj(coeq)⋅k)))
end
