module FinDomMap 

export FinDomFunctorMap

using StructEquality

using GATlab

using ...Cats, ..FinFunctors

import ..FinFunctors: FinDomFunctor, FinFunctor

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{DO,CO,DH,CH,DG, ObMap, HomMap, C<:AbsCat}
  ob_map::ObMap
  hom_map::HomMap
  dom::FinCat
  codom::C

  """
  When codom is actually a FinCat, there are a variety of 'formats' to represent
  the homs in the hom map.

  homtype = hom: the hom map `h` contains homs
            generator: contains raw generators 
            path (default): contains AbstractVectors of generators
  """
  function FinDomFunctorMap(o,h,d::FinCat,c::C; homtype=nothing, check=true) where {C<:AbsCat}
    DO, CO, DH, CH = impl_type.([d,c,d,c], [:Ob,:Ob,:Hom,:Hom])
    DG = gentype(d)

    homtype = isnothing(homtype) ? (c isa FinCat ? :path : :hom) : homtype
    h′ = if isnothing(h) 
      if isempty(hom_generators(d))
        Dict{DG,CH}()
      else 
        error("Cannot provide `nothing` for FinDomFunctorMap: domain has " 
              * "generators $(hom_generators(d))")
      end
    else 
      mapvals(f-> coerce_hom(c, f; homtype), h;) 
    end


    if check 
      for obgen in ob_generators(d)
        o[obgen] isa CO || error("Bad return type $(o[obgen]) not a $CO")
      end
      for homgen in hom_generators(d)
        h′[homgen] isa CH || error("Bad return type $(h[homgen]) not a $CH")
      end
    end
    
    length(o) == length(ob_generators(d)) ||
      error("Length of object map $o does not match domain $d")

    length(h′) == length(hom_generators(d)) ||
      error("Length of morphism map $h does not match domain $d")
    new{DO, CO, DH, CH, DG, typeof(o), typeof(h′), C}(o, h′, d, c)
  end
end


""" Interpret a presented hom as a hom in the codomain category """
function coerce_hom(cod::FinCat, f; homtype=:path)
  homtype == :hom && return f
  homtype == :generator && return to_hom(cod, f)
  homtype == :list && return foldl(compose[getvalue(cod)], to_hom.(Ref(cod), f))
  homtype == :path || error("Bad homtype $homtype")
  f isa Path || error("Bad path $f")
  isempty(f) && return id(cod, src(f))
  coerce_hom(cod, collect(f); homtype=:list)
end

function coerce_hom(::Cat, f; homtype=:path)
  homtype == :hom || error("Cannot coerce hom via $homtype for a Category")
  f
end

# FinDomFunctor instance
########################


"""
Note: in order to implement the findomfunctor interface, we need a 
way to decompose a 
"""
@instance ThFinDomFunctor{DO, CO, DH, CH, FinCat, C, DG
                          } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,OM,HM,C}
                            ] where {DO,CO,DH,CH,DG,OM,HM,C} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO)::CO = model.ob_map[x]

  function hom_map(x::DH)::CH 
    pth = decompose(getvalue(model.dom), x)
    isempty(pth) && return id(codom[model](), ob_map[model](src(pth)))
    foldl(compose[getvalue(model.codom)], gen_map[model].(pth))
  end
  gen_map(f::DG)::CH = model.hom_map[f]

end

# Constructors 
##############

# Check that cod is a FinCat
function FinFunctor(o,h,d::FinCat,c::FinCat; kw...) 
  FinDomFunctor′(FinDomFunctorMap(o,h,d,c; kw...)) |> validate
end

""" Wrap `FinDomFunctorMap` as a `FinDomFunctor` """
FinDomFunctor(o,h,d::FinCat,c::AbsCat; kw...) = 
  FinDomFunctor′(FinDomFunctorMap(o,h,d,c; kw...)) |> validate

# Check that cod is a FinCat
FinFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, cod::FinCat; kw...) = 
  FinDomFunctor(maps, dom, cod; kw...) |> validate

function FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, cod::AbsCat; kw...)
  D = getvalue(dom)
  if getvalue(D) isa FinCatGraph 
    FinDomFunctor(maps.V, maps.E, dom, cod; kw...)
  else 
    error("bad maps $maps for dom $(typeof(D))")
  end
end

function FinDomFunctor(ob_map, dom::FinCat, codom::AbsCat)
  is_discrete(dom) || error(
    "Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor′(FinDomFunctorMap(ob_map, [], dom, codom)) |> validate
end

function FinFunctor(ob_map, dom::FinCat, codom::FinCat)
  Hom = impl_type(codom, :Hom)
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor′(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom)) |> validate
end

FinFunctor(ob_map, ::Nothing, dom::FinCat, codom::FinCat) =
  FinDomFunctor′(ob_map, dom, codom) |> validate

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::Cat) =
  FinDomFunctor′(ob_map, dom, codom) |> validate

end # module
