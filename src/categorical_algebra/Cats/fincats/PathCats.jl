module PathCats

export PathCat, PathCatAsFinCat

using StructEquality

using GATlab 

import ......Graphs: src, tgt
using ......BasicSets: FinSet
using ...Paths: Path
using ..FinCats: ThFinCat
import ..FinCats: FinCat, dom, codom

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

ThPathCat.Meta.@wrapper PathCat

@struct_hash_equal struct PathCatAsFinCat{Ob,Hom}
  val::PathCat 
  PathCatAsFinCat(p::PathCat) = 
    new{impl_type(p,:Ob), impl_type(p,:Gen)}(p)
end

GATlab.getvalue(p::PathCatAsFinCat) = getvalue(p.val)
GATlab.equations(p::PathCatAsFinCat) = equations(getvalue(p))


@instance ThFinCat{Ob,Path{Ob,Gen},Gen,Path{Ob,Gen}} [
    model::PathCatAsFinCat{Ob,Gen}] where {Ob,Gen} begin

  src(g::Gen)::Ob = ThPathCat.src[getvalue(model)](g)
  
  tgt(g::Gen)::Ob = ThPathCat.tgt[getvalue(model)](g)

  dom(p::Path{Ob,Gen})::Ob = src(p)

  codom(p::Path{Ob,Gen})::Ob = tgt(p)

  id(x::Ob)::Path{Ob,Gen} = Path{Ob}(x,Gen)

  compose(f::Path{Ob,Gen})::Path{Ob,Gen} = f

  decompose(p::Path{Ob,Gen})::Path{Ob,Gen} = p

  ob_set()::FinSet = ob_set[getvalue(model)]()

  gen_set()::FinSet = gen_set[getvalue(model)]()

end

end # module