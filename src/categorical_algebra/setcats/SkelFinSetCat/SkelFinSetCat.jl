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

  id(A::FinSetInt)::FinFunction = FinFunction(FinSet(A)) # identity function

  function compose(f::FinFunction, g::FinFunction)::FinFunction
    codom[model](f) == dom[model](g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    FinFunction(f, g)
  end

end

@instance ThCategoryExplicitSets{FinSetInt, FinFunction} [model::SkelFinSet] begin

  ob_set() = SetOb(FinSetInt)

  hom_set() = SetOb(FinFunction)

end

@instance ThConcreteCategory{FinSetInt, FinFunction} [model::SkelFinSet] begin


  function lift(f::AbstractFunction, a::FinSetInt, b::FinSetInt) 
    getvalue(dom(f)) == a || error("Bad dom $a")
    getvalue(codom(f)) == b || error("Bad codom $b")
    f
  end
  ob_map(x::FinSetInt) = FinSet(x)
  hom_map(x::FinFunction) = x

end


@instance ThCategoryWithMonicsEpics{FinSetInt, FinFunction
                                } [model::SkelFinSet] begin

  is_monic(f::FinFunction) = is_monic(f)
  is_epic(f::FinFunction) = is_epic(f)
end

@instance ThCategoryColimitBase{FinSetInt,FinFunction} [model::SkelFinSet] begin 

  ob(t::AbsColimit)::FinSetInt = ob(t)

  apex(t::Multicospan)::FinSetInt = t.apex

end 

@instance ThCategoryLimitBase{FinSetInt,FinFunction} [model::SkelFinSet] begin 

  ob(t::AbsLimit)::FinSetInt = ob(t)

  apex(t::Multispan)::FinSetInt = t.apex
end 
