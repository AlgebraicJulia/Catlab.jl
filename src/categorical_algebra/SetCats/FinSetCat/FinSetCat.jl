export FinSetC 

using DataStructures, StructEquality, StaticArrays, GATlab

using ACSets: incident, copy_parts!
using GATlab


using ....Graphs, ....BasicSets,  ...Cats

using .ThCategory

# Structs
#########

""" Category of finite sets and functions """
@struct_hash_equal struct FinSetC end

 
@instance ThCategory{FinSet, FinFunction} [model::FinSetC] begin
  dom(f::FinFunction)::FinSet = dom(f)

  codom(f::FinFunction)::FinSet = codom(f)

  id(A::FinSet)::FinFunction = SetFunction(A) # identity function

  function compose(f::FinFunction, g::FinFunction)::FinFunction
    codom[model](f) == dom[model](g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end

end

@instance ThCategoryExplicitSets{FinSet, FinFunction, AbsSet
                                } [model::FinSetC] begin

  ob_set() = SetOb(FinSet)

  hom_set() = SetOb(FinFunction)

end

@instance ThCategoryColimitBase{FinSet,FinFunction,AbsSet,AbsColimit,
                                Multicospan} [model::FinSetC] begin 

  ob(t::AbsColimit)::FinSet = ob(t)

  apex(t::Multicospan)::FinSet = t.apex

end 


@instance ThCategoryLimitBase{FinSet,FinFunction,AbsSet,AbsLimit,
                                Multispan} [model::FinSetC] begin 

  ob(t::AbsLimit)::FinSet = ob(t)

  apex(t::Multispan)::FinSet = t.apex
end 


