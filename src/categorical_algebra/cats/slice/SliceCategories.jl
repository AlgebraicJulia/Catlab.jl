export SliceC, SliceOb, SliceHom

using StructEquality

using GATlab

import ....Theories: dom, codom, compose, id, ThCategory
using ....BasicSets: is_monic, is_epic
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


@struct_hash_equal struct SliceHom{ObT, HomT}
  dom::SliceOb{ObT, HomT}
  codom::SliceOb{ObT, HomT}
  hom::HomT
  function SliceHom(d::SliceOb{Ob, Hom}, c::SliceOb{Ob, Hom}, h::Hom; cat=nothing) where {Ob, Hom}
    𝒞 = WithModel(isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat)
    d.ob == dom(h) || error("Mismatch dom")
    c.ob == codom(h) || error("Mismatch dom")
    lft, rght = force(compose(𝒞, h, c.hom)), force(d.hom) 
    lft == rght || error("Doesn't commute: $lft ≠ $rght")
    new{Ob, Hom}(d, c, h)
  end
end

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


# If one wanted to have the homs be simply HomT rather than 
# SliceHoms, then one would be using "bare morphisms".
@instance ThCategoryExplicitSets{SliceOb{<:ObT, <:HomT}, SliceHom{<:ObT, <:HomT}
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

  function Hom(f::SliceHom{<:ObT, <:HomT}, x::SliceOb{<:ObT, <:HomT}, y::SliceOb{<:ObT, <:HomT})
    try
      Hom[model.cat](f, x.ob, y.ob)
    catch e
      error("morphism is not valid in base category", e)
    end
    compose[model.cat](f, y.hom; context=(a=x.ob, b=y.ob, c=model.over)) == x.hom ||
      error("commutativity of triangle does not hold")
    f
  end

  id(x::SliceOb{<:ObT, <:HomT}) = 
    SliceHom(x,x,id[model.cat](x.ob); cat=model.cat)

  dom(h::SliceHom{<:ObT, <:HomT}) = h.dom

  codom(h::SliceHom{<:ObT, <:HomT}) = h.codom

  function compose(f::SliceHom{<:ObT, <:HomT}, g::SliceHom{<:ObT, <:HomT})
    SliceHom(f.dom, g.codom, compose[model.cat](f.hom, g.hom))
  end

  # Actually we can get more specific than this with PredicatedSets.
  ob_set() = SetOb(SliceOb{ObT, HomT})
  hom_set() = SetOb(HomT)
end


"""
Pullbacks and pushouts are preserved by slicing, and therefore monos and epis.
"""
@instance ThCategoryWithMonicsEpics{SliceOb{<:ObT, <:HomT}, SliceHom{<:ObT, <:HomT}
                                } [model::SliceC{ObT, HomT}] where {ObT, HomT} begin 

  is_monic(α::SliceHom{<:ObT, <:HomT}) = is_monic[model.cat](α.hom)
  is_epic(α::SliceHom{<:ObT, <:HomT}) = is_monic[model.cat](α.hom)
end

