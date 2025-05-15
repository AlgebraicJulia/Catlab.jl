module FinCatCat 
export FinCatC

using StructEquality

using GATlab

using ....Theories: dom, codom, id, compose
using ..Categories: FinCat
using ..FinFunctors: FinDomFunctor, ThFinDomFunctor


""" Category of Finitely presented Categories """
@struct_hash_equal struct FinCatC end

@instance ThCategory{FinCat, FinDomFunctor} [model::FinCatC] begin

  dom(f::FinDomFunctor)::FinCat = ThFinDomFunctor.dom[getvalue(f)]()

  function codom(f::FinDomFunctor)::FinCat 
    c = ThFinDomFunctor.codom[getvalue(f)]() |> getvalue 
    c isa FinCat ? c : error("Bad codom $c")
  end

  id(c::FinCat) = FinDomFunctor(c)

  compose(f::FinDomFunctor, g::FinDomFunctor) = FinDomFunctor(f,g)

end

end # module
