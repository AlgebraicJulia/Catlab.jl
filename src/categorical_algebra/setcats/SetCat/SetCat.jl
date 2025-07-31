
export SetC

using StructEquality
using GATlab

using ....Theories
using ....BasicSets: FinSet, ConstantFunction, SetFunction, ProdSet, 
  SetOb, FinDomFunction, FinFunction, FinSetInt, ≃, AbstractFunction
using ...Cats


""" Category of sets and functions """
@struct_hash_equal struct SetC end

@instance ThCategoryExplicitSets{SetOb, SetFunction} [model::SetC] begin
  dom(f::SetFunction)::SetOb = dom(f)
  
  codom(f::SetFunction)::SetOb = codom(f)

  id(A::SetOb)::SetFunction = SetFunction(A)

  function compose(f::SetFunction, g::SetFunction)::SetFunction
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SetFunction(f, g)
  end

  ob_set() = SetOb(SetOb)

  hom_set() = SetOb(SetFunction)
end


@instance ThConcreteCategory{SetOb, SetFunction
                                } [model::SetC] begin

  ob_map(f::SetOb) = f
  hom_map(f::SetFunction) = f
  function lift(f::AbstractFunction, a::SetOb, b::SetOb)
    dom(f) == a || error("Bad dom $(dom(f)) ≠ $a")
    codom(f) == b || error("Bad codom $(codom(f)) ≠ $b")
    f
  end
end
