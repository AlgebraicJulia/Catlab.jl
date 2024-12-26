module MonoidalColimits 
export CocartesianMonoidal, oplus, mzero, ⊕

using GATlab

using .....Theories
import .....Theories: coproduct

using ...FreeDiagrams: DiscreteDiagram

using ..Coproducts: TypedCatWithCoproducts, CatWithCoproducts, ThCategoryUnbiasedCoproducts

import .ThCocartesianCategory: oplus, mzero

ThCocartesianCategory.Meta.@typed_wrapper CocartesianMonoidal

@instance ThCocartesianCategory{Ob, Hom} [model::TypedCatWithCoproducts{Ob,Hom}
] where {Ob,Hom} begin

  oplus(A::Ob, B::Ob) = ob(model, coproduct(model, A, B))

  function oplus(f::Hom, g::Hom)
    𝒞 = model
    ι1, ι2 = coproduct(𝒞, codom(f), codom(g))
    clim = coproduct(𝒞, dom(f), dom(g))
    copair(𝒞, clim, compose(𝒞, f,ι1), compose(𝒞, g,ι2))
  end

  function swap(A::Ob, B::Ob)
    AB = coproduct(model, A, B)
    BA = coproduct(model, B, A)
    copair(model, AB, coproj2(BA), coproj1(BA))
  end

  plus(A::Ob) = copair(id(A),id(A), getvalue(model))
  mzero() = ob(model, initial[getvalue(model)]())
  zero(A::Ob) = create(A, getvalue(model))
  coproj1(A::Ob, B::Ob) = coproj1(coproduct(model, A, B))
  coproj2(A::Ob, B::Ob) = coproj2(coproduct(model, A, B))

  copair(A::Hom, B::Hom) = error("TODO")

  id(A::Ob) = id(CatWithCoproducts(getvalue(model)), A)

  compose(A::Hom,B::Hom) = compose(CatWithCoproducts(getvalue(model)), A, B)

end

# oplus(m::WithModel{CocartesianMonoidal{Ob,Hom}}, As::AbstractVector{<:Ob}
#      ) where {Ob,Hom} = ob(coproduct(As, getvalue(getvalue(m))))
# function oplus(m::WithModel{CocartesianMonoidal{Ob,Hom}}, 
#                fs::AbstractVector{<:Hom}) where {Ob,Hom}
#   C = getvalue(getvalue(m))
#   ⊔ = coproduct(map(dom, fs), C)
#   ⊔′ = coproduct(map(codom, fs), C)
#   copair(⊔, map((x,y)->compose(C,x,y), fs, legs(⊔′)))
# end

# ⊕(m::WithModel{CocartesianMonoidal{Ob,Hom}}, xs::AbstractVector{<:Ob}) where {Ob,Hom} = oplus(m, xs...)

# ⊕(m::WithModel{CocartesianMonoidal{Ob,Hom}}, xs::AbstractVector{<:Hom}) where {Ob,Hom} = oplus(m, xs...)

# mzero(m::WithModel{CocartesianMonoidal{Ob,Hom}}) where {Ob,Hom} = 
#   ob(initial(getvalue(getvalue(m))))


end # module