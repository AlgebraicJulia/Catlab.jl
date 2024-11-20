module FinDomMap 

export FinDomFunctorMap

using StructEquality

using GATlab
import GATlab: getvalue

using ...Categories: Category, FinCat, Cat, obtype, homtype, FinCatGraph, Path,
                     ob_generators, hom_generators, gentype, PathCat, TypeCat,
                     compose
using ..FinFunctors: FinDomFunctorImpl, ThFinDomFunctor, mapvals
import ..FinFunctors: FinDomFunctor

""" Functor out of a finitely presented category given by explicit mappings.
"""
@struct_hash_equal struct FinDomFunctorMap{DO,CO,DH,CH,DG, ObMap, HomMap
    } <: FinDomFunctorImpl{DO,CO,DH,CH,DG}
  ob_map::ObMap
  hom_map::HomMap
  dom::FinCat
  codom::Category
  """
  """
  function FinDomFunctorMap(o,h,d::FinCat,c::Cat)
    DO, CO = obtype.([d,c])
    DH, CH = homtype.([d,c])
    DG = gentype(d)
    length(o) == length(ob_generators(d)) ||
      error("Length of object map $o does not match domain $d")
    length(h) == length(hom_generators(d)) ||
      error("Length of morphism map $h does not match domain $d")

    new{DO,CO,DH,CH,DG, typeof(o), typeof(h)}(o,h,d,c)
  end
end

"""
When codom is actually a FinCat, there are a variety of 'formats' to represent
the homs in the hom map.

homtype = hom: the hom map `h` contains homs
          generator: contains raw generators 
          path (default): contains AbstractVectors of generators
"""
function FinDomFunctorMap(o,h,d::FinCat,c::FinCat; homtype=:path)
  h′ = mapvals(h) do f 
    homtype == :hom && return f 
    homtype == :generator && return compose(c, Path(c, [f]))
    homtype == :path && return compose(c, Path(c, f))
  end
  FinDomFunctorMap(o,h′,d,Cat(c))
end

# FinDomFunctor instance
########################

@instance ThFinDomFunctor{DO,CO,DH,CH,DG, FinCat, Category
                          } [model::FinDomFunctorMap{DO,CO,DH,CH,DG,OM,HM}
                            ] where {DO,CO,DH,CH,DG,OM,HM} begin 
  dom() = model.dom

  codom() = model.codom

  ob_map(x::DO)::CO = model.ob_map[x]  

  gen_map(f::DG)::CH = model.hom_map[f]
end

# Constructors 
##############

FinDomFunctor(o,h,d::FinCat,c::Union{Cat,FinCat}; kw...) = 
  FinDomFunctor(FinDomFunctorMap(o,h,d,c; kw...))

function FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCat, 
                       cod::Union{FinCat,Cat}) 
  D = getvalue(dom)
  if D isa PathCat && getvalue(D) isa FinCatGraph 
    FinDomFunctor(maps.V, maps.E, dom, cod)
  else 
    error("bad maps $maps for dom $(typeof(D))")
  end
end

function FinDomFunctor(ob_map, dom::FinCat, codom::Cat)
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(FinDomFunctorMap(ob_map, empty(ob_map, Hom), dom, codom))
end

FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::Cat) =
  FinDomFunctor(ob_map, dom, codom)

end # module
