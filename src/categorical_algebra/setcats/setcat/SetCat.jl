
export SetC

using StructEquality
using GATlab

using ....Theories
using ....BasicSets: AbsSet, FinSet, ConstantFunction, SetFunction, ProdSet, 
  SetOb, FinDomFunction, ProdFinSet, FinFunction, FinSetInt, AbsFunction
using ...Cats


""" Category of sets and functions """
@struct_hash_equal struct SetC end

@instance ThCategoryExplicitSets{AbsSet, AbsFunction} [model::SetC] begin
  dom(f::AbsFunction)::AbsSet = dom(f)
  
  codom(f::AbsFunction)::AbsSet = codom(f)

  id(A::AbsSet)::AbsFunction = (A isa FinSet ? FinFunction : SetFunction)(A)

  function compose(f::AbsFunction, g::AbsFunction)::AbsFunction
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    df, cg = dom(f) isa FinSet, codom(g) isa FinSet
    F = df ? (cg ? FinFunction : FinDomFunction) : SetFunction
    F(f, g)
  end

  ob_set() = SetOb(AbsSet)

  hom_set() = SetOb(SetFunction)
end
