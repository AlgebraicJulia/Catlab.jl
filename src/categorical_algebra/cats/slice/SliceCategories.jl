export SliceC, SliceOb

using StructEquality

using GATlab

import ....Theories: dom, codom, compose, id, ThCategory
import ....BasicSets: force

using ...Cats

"""
The data of the object of a slice category (say, some category C sliced over an
object X in Ob(C)) is the data of a homomorphism in Hom(A,X) for some ob A.
"""
@struct_hash_equal struct SliceOb{ObT, HomT}
  ob::ObT
  hom::HomT
end

SliceOb(hom; cat=nothing) = 
  SliceOb(isnothing(cat) ? dom(hom) : dom[cat](hom), hom)

# We want to use this for potentially many theories (e.g. the various (co)limit
# theories) so it doesn't make sense to store a wrapped model. Just store raw 
# model.
"""
The data of the morphism of a slice category (call it h, and suppose a category
C is sliced over an object X in Ob(C)) between objects f and g is a homomorphism
in the underlying category that makes the following triangle commute.

```
   h
A --> B
f ↘ ↙ g
   X
```
"""
@struct_hash_equal struct SliceC{ObT, HomT}
  cat::Any 
  over::ObT
  function SliceC(cat::Category, over)
    cat = getvalue(cat) # confirmed our input is *at least* a model of ThCategory
    new{impl_types(cat, ThCategory)...}(cat, over)
  end
end

using .ThCategoryExplicitSets

@instance ThCategoryExplicitSets{SliceOb{<:ObT, <:HomT}, HomT
                                } [model::SliceC{ObT, HomT}
                                  ] where {ObT, HomT} begin
  function Ob(x::SliceOb{<:ObT, <:HomT})
    try
      Ob[model.cat](x.ob)
    catch e
      error("ob is not valid", e)
    end
    try
      Hom[model.cat](x.hom, x.ob, model.over)
    catch e
      error("hom is not valid", e)
    end
    x
  end

  function Hom(f::HomT, x::SliceOb{<:ObT, <:HomT}, y::SliceOb{<:ObT, <:HomT})
    try
      Hom[model.cat](f, x.ob, y.ob)
    catch e
      error("morphism is not valid in base category", e)
    end
    compose[model.cat](f, y.hom; context=(a=x.ob, b=y.ob, c=model.over)) == x.hom ||
      error("commutativity of triangle does not hold")
    f
  end

  id(x::SliceOb{<:ObT, <:HomT}) = id[model.cat](x.ob)

  dom(::HomT; context) = context[:dom]

  codom(::HomT; context) = context[:codom]

  function compose(f::HomT, g::HomT; context=nothing)
    context=isnothing(context) ? nothing : map(x -> x.ob, context)
    compose[model.cat](f, g; context)
  end

  # Actually we can get more specific than this with PredicatedSets.
  ob_set() = SetOb(SliceOb{ObT, HomT})
  hom_set() = SetOb(HomT)
end
