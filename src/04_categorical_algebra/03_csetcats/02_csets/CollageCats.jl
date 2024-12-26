module CollageCats 

export CollageCat, CollageDomIncl, CollageCodomIncl

using MLStyle, StructEquality
using GATlab

using .....BasicSets
using ....Cats
using ..Heteromorphisms

@struct_hash_equal struct CollageCat{DO,CO,DH,CH,Het}
  domcat::Category 
  codcat::Category
  hetero::Hetero

  function CollageCat(d::Category, c::Category, h::Hetero)
    # TODO validate types of d and c match up with h
    Ts = impl_type.([d,d,c,c,h],[:Ob,:Hom,:Ob,:Hom,:Het])
    new{Ts...}(d,c,h)
  end
end


@instance ThCategoryExplicitSets{Tagged([DO, CO]), Tagged([DH,CH,Het]), AbsSet
                                } [model::CollageCat{DO,CO,DH,CH,Het}
                                  ] where {DO,CO,DH,CH,Het} begin
  codom(f::Tagged([DH,CH,Het])) = @match f begin 
    _ => error("HERE $f")
  end

  ob_set() = SumSet(ob_set(model.domcat), ob_set(model.codcat))

  hom_set() = SumSet(hom_set(model.domcat), hom_set(model.codcat), impl_type(model.hetero, :Het))

  function id(x::Tagged([DO, CO]))
    @match x begin 
      _ => error("HERE $x")
    end
  end
  
  function compose(f::Tagged([DH,CH,Het]), g::Tagged([DH,CH,Het]))
    @match (f,g) begin 
      _ => error("HERE $f $g")
    end
  end
end

""" Monic functor from domain cat of collage into the collage category """
@struct_hash_equal struct CollageDomIncl{DO,CO,DH,CH,Het}
  c::CollageCat{DO,CO,DH,CH,Het}
end

GATlab.getvalue(c::CollageDomIncl) = c.c

@instance ThFunctor{DO,Tagged([DO,CO]),DH,Tagged([DH,CH,Het]), Category} [
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

@instance ThFunctor{DO,Tagged([DO,CO]),DH,Tagged([DH,CH,Het]), Category} [
  model::CollageCodomIncl{DO,DH,CO,CH,Het}] where {DO,DH,CO,CH,Het} begin 

  dom() = getvalue(model).codcat
  codom() = Category(getvalue(model))
  ob_map(x::DO) = TaggedElem(x, 2)
  hom_map(x::DH) = TaggedElem(x, 2)
end

end # module
