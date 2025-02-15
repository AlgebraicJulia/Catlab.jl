module MonoidalColimits 
export CocartesianMonoidal, oplus, mzero, ⊕, coproduct

using GATlab

using .....Theories

using ...Cats: DiscreteDiagram, Multicospan, Category, legs

using ..Coproducts: TypedCatWithCoproducts, CatWithCoproducts, 
                    ThCategoryUnbiasedCoproducts, coproduct
import ..LimitsColimits: bundle_leg
import .ThCocartesianCategory: oplus, mzero, copair

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

  function copair(A::Hom, B::Hom) 
    m = getvalue(model)
    copair[m](coproduct[m](dom(A), dom(B)), A, B)
  end

  id(A::Ob) = id(CatWithCoproducts(getvalue(model)), A)

  compose(A::Hom,B::Hom) = compose(CatWithCoproducts(getvalue(model)), A, B)
end

function copair(m::WithModel{<:TypedCatWithCoproducts}, hs::AbstractVector; context=nothing)
  h, hrest... = hs 
  foldl((x,y)->copair(m, x,y; context), hrest; init=h)
end

function oplus(m::WithModel{<:TypedCatWithCoproducts}, hs::AbstractVector; context=nothing)
  h, hrest... = hs 
  foldl((x,y)->oplus(m, x,y; context), hrest; init=h)
end


bundle_leg(cospan::Multicospan, is::AbstractVector{Int}, m  
          )  = copair(CocartesianMonoidal(TypedCatWithCoproducts(m)), 
                      legs(cospan)[is])

end # module
