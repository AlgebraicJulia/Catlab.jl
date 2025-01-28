
export SetC

using StructEquality
using GATlab

using ....Theories
using ....BasicSets: AbsSet, FinSet, ConstantFunction, SetFunction, ProdSet, 
  SetOb, FinDomFunction, ProdFinSet, FinFunction, FinSetInt
using ...Cats


""" Category of sets and functions """
@struct_hash_equal struct SetC end

@instance ThCategoryExplicitSets{AbsSet, SetFunction,AbsSet} [model::SetC] begin
  dom(f::SetFunction)::AbsSet = dom(f)
  
  codom(f::SetFunction)::AbsSet = codom(f)

  id(A::AbsSet)::SetFunction = SetFunction(A) # identity function

  function compose(f::SetFunction, g::SetFunction)::SetFunction
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end

  ob_set() = SetOb(AbsSet)

  hom_set() = SetOb(SetFunction)
end
