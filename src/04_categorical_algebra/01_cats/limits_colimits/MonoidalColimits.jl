module MonoidalColimits 
export CocartesianMonoidal, oplus, mzero, ⊕

using GATlab

using .....Theories

using ...FreeDiagrams: DiscreteDiagram

using ..Coproducts: TypedCatWithCoproducts, CatWithCoproducts, ThCategoryUnbiasedCoproducts

using .ThCategoryUnbiasedCoproducts: coproduct
import .ThCocartesianCategory: oplus, mzero

ThCocartesianCategory.Meta.@typed_wrapper CocartesianMonoidal

@instance ThCocartesianCategory{Ob, Hom} [model::TypedCatWithCoproducts{Ob,Hom,X1,X2,X3,X4}
                                         ] where {Ob,Hom,X1,X2,X3,X4} begin
  @import Ob, Hom, dom, codom, compose, ⋅, →, id, copair

  oplus(A::Ob, B::Ob) = ob(model, coproduct(model, DiscreteDiagram([A, B])))

  function oplus(f::Hom, g::Hom)
    𝒞 = model
    ι1, ι2 = coproduct(𝒞, DiscreteDiagram([codom(f), codom(g)]))
    clim = coproduct(𝒞, DiscreteDiagram([dom(f), dom(g)]))
    copair(𝒞, clim, compose(𝒞, f,ι1), compose(𝒞, g,ι2))
  end

  function swap(A::Ob, B::Ob)
    AB = coproduct(model, DiscreteDiagram([A, B]))
    BA = coproduct(model, DiscreteDiagram([B, A]))
    copair(model, AB, coproj2(BA), coproj1(BA))
  end

  plus(A::Ob) = copair(id(A),id(A), getvalue(model))
  mzero() = ob(model,initial(model))
  zero(A::Ob) = create(A, getvalue(model))
  coproj1(A::Ob, B::Ob) = coproj1(coproduct(model, DiscreteDiagram([A, B])))
  coproj2(A::Ob, B::Ob) = coproj2(coproduct(model, DiscreteDiagram([A, B])))
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