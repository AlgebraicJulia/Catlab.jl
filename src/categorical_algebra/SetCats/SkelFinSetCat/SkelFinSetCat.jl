export SkelFinSet

using StructEquality
using GATlab
using ....Theories, ....BasicSets,  ...Cats

""" 
Skeleton of category of sets and functions. Objects are {1,2,...,n} for some 
n ∈ ℕ, represented as `FinSetInt`. Morphisms are `SetFunctions` whose domain 
and codomain are `FinSet(FinSetInt(n::Int))`.
"""
@struct_hash_equal struct SkelFinSet end


@instance ThCategory{FinSetInt, FinFunction} [model::SkelFinSet] begin
  dom(f::FinFunction)::FinSetInt = getvalue(dom(f))

  codom(f::FinFunction)::FinSetInt = getvalue(codom(f))

  id(A::FinSetInt)::FinFunction = SetFunction(FinSet(A)) # identity function

  function compose(f::FinFunction, g::FinFunction)::FinFunction
    codom[model](f) == dom[model](g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end

end

@instance ThCategoryExplicitSets{FinSetInt, FinFunction, AbsSet
                                } [model::SkelFinSet] begin

  ob_set() = SetOb(FinSetInt)

  hom_set() = SetOb(FinFunction)

end

@instance ThCategoryColimitBase{FinSetInt,FinFunction,AbsSet,AbsColimit,
                                Multicospan} [model::SkelFinSet] begin 

  ob(t::AbsColimit)::FinSetInt = ob(t)

  apex(t::Multicospan)::FinSetInt = t.apex

end 

@instance ThCategoryLimitBase{FinSetInt,FinFunction,AbsSet,AbsLimit,
                                Multispan} [model::SkelFinSet] begin 

  ob(t::AbsLimit)::FinSetInt = ob(t)

  apex(t::Multispan)::FinSetInt = t.apex
end 
