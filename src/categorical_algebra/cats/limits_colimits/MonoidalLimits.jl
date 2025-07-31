module MonoidalLimits 
export CartesianMonoidal, otimes, munit, ⊗

using GATlab

using .....Theories

using ..Products: TypedCatWithProducts, CatWithProducts, ThCategoryUnbiasedProducts, product

import .ThCartesianCategory: otimes, munit

ThCartesianCategory.Meta.@typed_wrapper CartesianMonoidal


# This is the sort of thing we expect to be able to do with a simple TheoryMap 
# migration once AlgStructs are integrated into GATlab

""" Define cartesian monoidal structure using limits.

Implements an instance of [`ThCartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
@instance ThCartesianCategory{Ob, Hom} [model::TypedCatWithProducts{Ob,Hom}
                                       ] where {Ob,Hom} begin

  otimes(A::Ob, B::Ob)::Ob = ob(product(CatWithProducts(getvalue(model)), A, B))

  function otimes(f::Hom, g::Hom)::Hom
    𝒞 = CatWithProducts(getvalue(model))
    π1, π2 = product(𝒞, dom(f), dom(g))
    pair(𝒞, product(𝒞, codom(f), codom(g)), compose(𝒞, π1,f), compose(𝒞, π2, g))
  end

  function braid(A::Ob, B::Ob)
    𝒞 = CatWithProducts(getvalue(model))
    AB, BA = product(𝒞, A, B), product(𝒞, B, A)
    pair(𝒞, BA, proj2(AB), proj1(AB))
  end

  munit()::Ob = ob(terminal[getvalue(model)]())

  mcopy(A::Ob) = let 𝒞 = CatWithProducts(getvalue(model)); 
    pair(𝒞, product(𝒞, A, A), id(𝒞,A), id(𝒞,A)) 
  end

  proj1(A::Ob, B::Ob) = proj1(product(CatWithProducts(getvalue(model)), A, B))

  proj2(A::Ob, B::Ob) = proj2(product(CatWithProducts(getvalue(model)), A, B))

  id(A::Ob) = id(CatWithProducts(getvalue(model)), A)
  function pair(A::Hom, B::Hom) 
    m = getvalue(model)
    pair[m](product[m](codom(A), codom(B)), A, B)
  end
  delete(A::Ob) = delete[getvalue(model)](A)
  compose(A::Hom,B::Hom) = compose(CatWithProducts(getvalue(model)), A, B)
end

end # module
