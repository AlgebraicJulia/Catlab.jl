module CollageCats 

export CollageCat, CollageDomIncl, CollageCodomIncl

using MLStyle, StructEquality
using GATlab

using .....BasicSets
using ....Cats
using ..Heteromorphisms
using ..CSets: ACSetCategory, entity_cat, attrtypes, acset_schema, attr_cat, prof_cat

"""
The types of of DO/CO and DH/CH/Het are expected to be disjoint, so we 
can use union rather than sum. 
"""
@struct_hash_equal struct CollageCat{DO,CO,DH,CH,Het}
  domcat::Category 
  codcat::Category
  hetero::Hetero

  function CollageCat(d::Category, c::Category, h::Hetero)
    # TODO validate types of d and c match up with h
    DO,CO,DH,CH,_ = Ts = impl_type.([d,c,d,c,h],[:Ob,:Ob,:Hom,:Hom,:Het])
    HDO, HCO, HDom,HCod = impl_type.(Ref(h),[:DomOb,:CodOb,:DomHom,:CodHom])
    HDO == DO || error(
      "Hetero dom ob does not match in collage cat: $DO ≠ $HDO")

    HCO == CO || error(
      "Hetero codom ob does not match in collage cat: $CO ≠ $HCO")
  
    DH == HDom || error(
      "Hetero dom does not match in collage cat: $DH ≠ $HDom")
    CH == HCod || error(
      "Hetero codom does not match in collage cat: $CH ≠ $HCod")
    new{Ts...}(d,c,h)
  end
end

@instance ThCategoryExplicitSets{Union{DO, CO}, Union{DH,CH,Het}
                                } [model::CollageCat{DO,CO,DH,CH,Het}
                                  ] where {DO,CO,DH,CH,Het} begin

  ob_set()::SetOb = UnionSet(ob_set.([model.domcat,model.codcat])) |> SetOb

  function hom_set()::SetOb
    UnionSet([hom_set.([model.domcat,model.codcat])..., 
            SetOb(impl_type(model.hetero, :Het))]) |> SetOb
  end

  function dom(x::Union{DH,CH,Het})::Union{DO, CO}
    𝒞 = if x isa DH 
      model.domcat
    elseif x isa CH 
      model.codcat 
    elseif x isa Het 
      model.hetero
    else 
      error("Bad type $x ($DH, $CH, $Het)")
    end 
    dom(𝒞, x)
  end

  function codom(x::Union{DH,CH,Het})::Union{DO, CO}
    𝒞 = if x isa DH
      model.domcat
    elseif x isa CH
      model.codcat
    else
      model.hetero
    end
    codom(𝒞, x)
  end

  function id(x::Union{DO, CO})::Union{DH,CH,Het}
    if x isa DO
      id(model.domcat, x)
    else 
      id(model.codcat, x)
    end
  end
  
  function compose(f::Union{DH,CH,Het}, g::Union{DH,CH,Het}
                  )::Union{DH,CH,Het}
    if f isa DH && g isa DH 
      compose(model.domcat, f, g)
    elseif f isa CH && g isa CH 
      compose(model.codcat, f, g)
    elseif f isa DH && g isa Het 
      pre(model.hetero, f, g)
    elseif f isa Het && G isa CH 
      post(model.hetero, v₁, v₂)
    else
      error("Bad types $f $g ($DH, $CH, $Het)")
    end
  end
end

""" Monic functor from domain cat of collage into the collage category """
@struct_hash_equal struct CollageDomIncl{DO,CO,DH,CH,Het}
  c::CollageCat{DO,CO,DH,CH,Het}
end

GATlab.getvalue(c::CollageDomIncl) = c.c

@instance ThFunctor{DO,Tagged([DO,CO]),DH,Tagged([DH,CH,Het]), Cat, Cat} [
  model::CollageDomIncl{DO,DH,CO,CH,Het}] where {DO,DH,CO,CH,Het} begin 

  dom() = getvalue(model).domcat
  codom() = Category(getvalue(model))
  ob_map(x::DO) = TaggedElem(x, 1)
  hom_map(x::DH) = TaggedElem(x, 1)
end


""" Monic functor from domain cat of collage into the collage category """
@struct_hash_equal struct CollageCodomIncl{DO,CO,DH,CH,Het}
  c::CollageCat{DO,CO,DH,CH,Het}
end

GATlab.getvalue(c::CollageCodomIncl) = c.c

@instance ThFunctor{DO,Tagged([DO,CO]),DH,Tagged([DH,CH,Het]), Cat, Cat} [
  model::CollageCodomIncl{DO,DH,CO,CH,Het}] where {DO,DH,CO,CH,Het} begin 

  dom() = getvalue(model).codcat
  codom() = Category(getvalue(model))
  ob_map(x::DO) = TaggedElem(x, 2)
  hom_map(x::DH) = TaggedElem(x, 2)
end


# Constructor via ACSetCategory
###############################

function CollageCat(C::ACSetCategory)
  𝒞 = Category(entity_cat(C))
  acats = Dict{Any,Category}(o=>Category(attr_cat(C, o)) for o in attrtypes(acset_schema(C)))
  𝒟 = Category(NamedCoproductCat(acats))
  ps = Dict(o=>Hetero(prof_cat(C, o)) for o in attrtypes(acset_schema(C)))
  𝒫 = Hetero(CoproductHeteroMorphism(ps, 𝒞))
  CollageCat(𝒞, 𝒟, 𝒫)
end


end # module
