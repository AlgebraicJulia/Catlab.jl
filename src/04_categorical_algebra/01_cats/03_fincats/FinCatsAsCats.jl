module FinCatsAsCats

using StructEquality
using GATlab 

using .....BasicSets: AbsSet
using ...Categories: ThCategoryExplicitSets
import ...Categories: Category

using ..FinCats: ThFinCat, hom_set
import ..FinCats: FinCat

using .ThFinCat

"""
Cast a model of a FinCat to a model of ThCategoryExplicitSets
"""
@struct_hash_equal struct FinCatAsCat{Ob,Hom}
  val::FinCat
  FinCatAsCat(f::FinCat) = new{impl_type(f, :Ob), impl_type(f, :Hom)}(f)
end

GATlab.getvalue(f::FinCatAsCat) = f.val

@instance ThCategoryExplicitSets{Ob,Hom,AbsSet} [model::FinCatAsCat{Ob,Hom}
                                                ] where {Ob,Hom} begin

  dom(f::Hom) = dom(getvalue(model), f)

  codom(f::Hom) = codom(getvalue(model), f)

  id(x::Ob) = id(getvalue(model), x)

  function compose(f::Hom, g::Hom)
    c = getvalue(model)
    compose(c, vcat(decompose(c, f), decompose(c, g)))
  end

  ob_set() = ob_set(getvalue(model))

  hom_set() = hom_set(getvalue(model))
end


Category(f::FinCat) = Category(FinCatAsCat(f))

function FinCat(C::Category) 
  c = getvalue(C)
  if c isa FinCatAsCat 
    getvalue(c)
  else 
    error("Cannot convert a $c into a FinCat")
  end 
end

end # module