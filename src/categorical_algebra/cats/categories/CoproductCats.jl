module CoproductCats
export CoproductCat, NamedCoproductCat

using StructEquality

using GATlab 

using .....BasicSets
using ..Categories

using .ThCategory

""" Data structure to represent coproducts of categories in an unbiased way. 

The types of the Ob/Hom are tagged SumSets.
"""
@struct_hash_equal struct CoproductCat{O,H}
  cats::Vector{Category}
  function CoproductCat(cats::Vector{Category})
    SumO = eltype(SetOb(SumSet(ob_set.(cats))))
    SumH = eltype(SetOb(SumSet(hom_set.(cats))))
    new{SumO, SumH}(cats)
  end
end 

GATlab.getvalue(x::CoproductCat) = x.cats

Base.getindex(x::CoproductCat, i::Int) = x.cats[i]

@instance ThCategoryExplicitSets{O,H} [model::CoproductCat{O,H}
                                      ] where {O,H} begin 

  function id(x::O)::H 
    t = gettag(x); 
    TaggedElem(id(model[t], getvalue(x)), t)
  end

  function dom(x::H)::O 
    t = gettag(x)
    TaggedElem(dom(model[t], getvalue(x)), t)
  end

  function codom(x::H)::O 
    t = gettag(x)
    TaggedElem(codom(model[t], getvalue(x)), t)
  end

  function compose(x::H,y::H)::H
    tx, ty = gettag.([x,y])
    tx == ty || error("Cannot compose $x $y")
    TaggedElem(compose(model[tx], getvalue(x), getvalue(y)), tx)
  end

  ob_set()::SetOb = SumSet(ob_set.(getvalue(model))) |> SetOb

  hom_set()::SetOb = SumSet(hom_set.(getvalue(model))) |> SetOb

end

# NamedCoproductCat #
#####################


""" Data structure to represent coproducts of categories in an unbiased way. 

The types of the Ob/Hom are tagged SumSets.
"""
@struct_hash_equal struct NamedCoproductCat{O,H}
  cats::Dict{Any, Category}
  function NamedCoproductCat(cats::Dict{Any, Category})
    SumO, SumH = [Tagged(Dict{Any,Type}(k=>impl_type(c, x) for (k,c) in cats) )
                  for x in [:Ob, :Hom]]
    new{SumO, SumH}(cats)
  end
end 

GATlab.getvalue(x::NamedCoproductCat) = x.cats

Base.getindex(x::NamedCoproductCat, i::Int) = x.cats[i]

@instance ThCategoryExplicitSets{O,H} [model::NamedCoproductCat{O,H}
                                             ] where {O,H} begin 

  function id(x::O)::H 
    t = gettag(x); 
    TaggedElem(id(model[t], getvalue(x)), t)
  end

  function dom(x::H)::O 
    t = gettag(x)
    TaggedElem(dom(model[t], getvalue(x)), t)
  end

  function codom(x::H)::O 
    t = gettag(x)
    TaggedElem(codom(model[t], getvalue(x)), t)
  end

  ob_set()::SetOb = SumSet(ob_set.(collect(values(getvalue(model))))) |> SetOb

  function hom_set()::SetOb 
    hs = Vector{SetOb}(hom_set.(collect(values(getvalue(model)))))
    SumSet(hs) |> SetOb
  end

  function compose(x::H,y::H)::H
    tx, ty = gettag.([x,y])
    tx == ty || error("Cannot compose $x $y")
    TaggedElem(compose(model[tx], getvalue(x), getvalue(y)), tx)
  end
end

end # module
