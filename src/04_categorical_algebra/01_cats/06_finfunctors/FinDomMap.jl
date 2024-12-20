module FinDomMap 

export FinDomFunctorMap

using StructEquality

using GATlab
import GATlab: getvalue

using ...Paths: Path
using ...Categories: Category, Cat, AbsCat, obtype, homtype,  compose, TypeCat
using ...FinCats: FinCat, gentype, ob_generators, hom_generators, FinCatGraph, PathCat

using ..FinFunctors: ThFinDomFunctor, mapvals
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
  function FinDomFunctorMap(o,h,d::FinCat,c::C; homtype=nothing) where {C<:AbsCat}
    @show homtype
    homtype = isnothing(homtype) ? (c isa FinCat ? :path : :hom) : homtype
    @show homtype
    h′ = mapvals(f-> coerce_hom(c, f; homtype), h) 

    DO, CO = impl_type.([d,c], :Ob)
    DH, CH = impl_type.([d,c], :Hom)
    DG = gentype(d)

    length(o) == length(ob_generators(d)) ||
      error("Length of object map $o does not match domain $d")

    length(h) == length(hom_generators(d)) ||
      error("Length of morphism map $h does not match domain $d")
    @show h′
    new{DO, CO, DH, CH, DG, typeof(o), typeof(h′), C}(o, h′, d, c)
  end
end


""" Interpret a presented hom as a hom in the codomain category """
function coerce_hom(cod::FinCat, f; homtype=:path)
  @show f
  @show homtype
  homtype == :hom && return f 
  homtype == :generator && return compose(cod, Path(cod, [f]))
  homtype == :path && return compose(cod, Path(cod, f))
end

function coerce_hom(::Cat, f; homtype=:path)
  homtype == :hom || error("Cannot coerce hom via $homtype for a Category")
  f
end

# FinDomFunctor instance
########################

@instance ThFinDomFunctor{DO,CO,DH,CH,DG, FinCat, C
                          } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,OM,HM,C}
                            ] where {DO,CO,DH,CH,DG,OM,HM,C} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO)::CO = model.ob_map[x]  

  gen_map(f::DG)::CH = model.hom_map[f]

end

# Constructors 
##############

# Check that cod is a FinCat
FinFunctor(o,h,d::FinCat,c::FinCat; kw...) = 
  FinFunctor(FinDomFunctorMap(o,h,d,c; kw...))

""" Wrap `FinDomFunctorMap` as a `FinDomFunctor` """
FinDomFunctor(o,h,d::FinCat,c::AbsCat; kw...) = 
  FinDomFunctor(FinDomFunctorMap(o,h,d,c; kw...))

# Check that cod is a FinCat
FinFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, cod::FinCat) = 
  FinDomFunctor(maps, dom, cod)

function FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, cod::AbsCat) 
  D = getvalue(dom)
  if D isa PathCat && getvalue(D) isa FinCatGraph 
    FinDomFunctor(maps.V, maps.E, dom, cod)
  else 
    error("bad maps $maps for dom $(typeof(D))")
  end
end

function FinDomFunctor(ob_map, dom::FinCat, codom::AbsCat)
  is_discrete(dom) || error(
    "Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

function FinFunctor(ob_map, dom::FinCat, codom::FinCat)
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

FinFunctor(ob_map, ::Nothing, dom::FinCat, codom::FinCat) =
  FinDomFunctor(ob_map, dom, codom)

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::Cat) =
  FinDomFunctor(ob_map, dom, codom)

end # module
