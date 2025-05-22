module PathCats

export PathCat, PathCatAsFinCat

using StructEquality

using GATlab 

import ......Graphs: src, tgt
using ......BasicSets: FinSet, SetOb
using ...Paths: Path
using ..FinCats: ThFinCat
import ..FinCats: FinCat, dom, codom, decompose

# Theory of Categories where homs are presumed to be paths of generators
########################################################################

"""
Morphisms assumed to be paths, composed by concatenation.
"""
@theory ThPathCat begin 
  Ob::TYPE 
  Gen(src::Ob, tgt::Ob)::TYPE
  Set′::TYPE{FinSet} 
  Eqs::TYPE # Vector{Pair{Vector{Gen}, Vector{Gen}}}
  ob_set()::Set′
  gen_set()::Set′
  eqs()::Eqs
end
  
# Wrapper type for models of `ThPathCat`
#######################################

ThPathCat.Meta.@typed_wrapper PathCat

# @struct_hash_equal struct PathCatAsFinCat{Ob,Hom}
#   val::PathCat 
#   PathCatAsFinCat(p::PathCat) = 
#     new{impl_type(p,:Ob), impl_type(p,:Gen)}(p)
# end

# GATlab.getvalue(p::PathCatAsFinCat) = getvalue(p.val)
GATlab.equations(p::PathCat) = equations(getvalue(p))

decompose(::PathCat, p::Path)::Path = p

@instance ThFinCat{Ob,Path{Ob,Gen},Gen} [
    model::PathCat{Ob,Gen}] where {Ob,Gen} begin

  src(g::Gen)::Ob = ThPathCat.src[getvalue(model)](g)
  
  tgt(g::Gen)::Ob = ThPathCat.tgt[getvalue(model)](g)

  dom(p::Path{Ob,Gen})::Ob = src(p)

  codom(p::Path{Ob,Gen})::Ob = tgt(p)

  id(x::Ob)::Path{Ob,Gen} = Path{Ob}(x,Gen)

  compose(f::Path{Ob,Gen}, g::Path{Ob,Gen})::Path{Ob,Gen} = vcat(f, g)

  ob_set()::SetOb = SetOb(getvalue(ob_set[getvalue(model)]()))

  gen_set()::FinSet = gen_set[getvalue(model)]()

  hom_set()::SetOb = SetOb(Path{Ob,Gen})

  to_hom(g::Gen) = Path{Ob,Gen}([g], src[model](g), tgt[model](g))

end

end # module