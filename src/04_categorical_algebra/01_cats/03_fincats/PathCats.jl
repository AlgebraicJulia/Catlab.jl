module PathCats

export PathCat 

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
  Set′::TYPE  # FinSet
  Eqs::TYPE # Vector{Pair{Vector{Gen}, Vector{Gen}}}
  ob_set()::Set′
  gen_set()::Set′
  eqs()::Eqs
end

""" Any type which subtypes this ought implement ThPathCat """
abstract type PathCatImpl{Ob,Gen} end
  
# Wrapper type for models of `ThPathCat`
#######################################

""" 
Wrapper type for models of `ThPathCat`

A finitely presented (but not necessarily finite!) category.
"""
@struct_hash_equal struct PathCat{Ob,Gen}
  impl::PathCatImpl{Ob,Gen}
  function PathCat(impl::PathCatImpl{Ob,Gen}) where {Ob,Gen}
    implements(impl, ThPathCat) || error("Model isn't a PathCat")
    new{Ob,Gen}(impl)
  end
end

GATlab.getvalue(p::PathCat) = p.impl

# 
src(p::PathCat, x) = ThPathCat.src[getvalue(p)](x)

tgt(p::PathCat, x) = ThPathCat.tgt[getvalue(p)](x)

dom(::PathCat, x::Path) = src(x)

codom(::PathCat, x::Path) = tgt(x)


ob_set(p::PathCat) = ThPathCat.ob_set[getvalue(p)]()

gen_set(p::PathCat) = ThPathCat.gen_set[getvalue(p)]()



GATlab.equations(p::PathCat) = equations(getvalue(p))


@instance ThFinCat{Ob,Path{Ob,Gen},Gen,Path{Ob,Gen},FinSet} [
    model::PathCat{Ob,Gen}] where {Ob,Gen} begin

  src(g::Gen)::Ob = ThPathCat.src[getvalue(model)](g)
  
  tgt(g::Gen)::Ob = ThPathCat.tgt[getvalue(model)](g)

  dom(p::Path{Ob,Gen})::Ob = src(p)

  codom(p::Path{Ob,Gen})::Ob = tgt(p)

  id(x::Ob)::Path{Ob,Gen} = Path{Ob,Gen}(x)

  compose(f::Path{Ob,Gen})::Path{Ob,Gen} = f

  decompose(p::Path{Ob,Gen})::Path{Ob,Gen} = p

  ob_set()::FinSet = ob_set[getvalue(model)]()

  gen_set()::FinSet = gen_set[getvalue(model)]()

end

FinCat(m::PathCatImpl) = FinCat(PathCat(m))

end # module