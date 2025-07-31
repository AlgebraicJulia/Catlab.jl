"""    specialize(::Type{T}, d::FreeDiagram) 

Interpret a FreeDiagram as a specific implementation of type T, e.g. DiscreteDiagram, Multispan, etc. 
"""
module Specialize 
export specialize 

using ..FreeDiagrams
import ..FreeDiagrams: specialize
using .ThFreeDiagram

"""
Try to replace a FreeDiagram implementation with the 'simplest' equivalent
FreeDiagram implementation. This will effect the efficiency of algorithms which
dispatch on the implementation of the FreeDiagram but otherwise should cause 
no changes w/r/t the FreeDiagram interface (perhaps the E/V types are different,
but their cardinalities should be the same).
"""
function specialize(d::FreeDiagram; kw...)::FreeDiagram
  len = length
  spec(T) = FreeDiagram(specialize(T, d; kw...))
  o, h, os = obset(d), homset(d), ob(d)
  if isempty(h) 
    isempty(o) && return spec(EmptyDiagram, d)
    len(os) == 1 && return spec(SingletonDiagram)
    len(os) == 2 && return spec(ObjectPair)
    return spec(DiscreteDiagram)
  end
  srcs, tgts = src.(Ref(d), h), tgt.(Ref(d), h)
  st_obs = sort(collect(union(srcs, tgts))) # all obs which are src or tgt
  eqs, eqt = allequal(srcs), allequal(tgts)

  (eqs && eqt && st_obs == sort(collect(o))
    && return spec(ParallelMorphisms))
  eqt && return spec(Multicospan)
  eqs && return spec(Multispan)
  isempty(srcs ∩ tgts) && return spec(Bipartite)
  if len(srcs) == len(unique(srcs)) && len(tgts) == len(unique(tgts))
    start, ending = setdiff(srcs,tgts), setdiff(tgts,srcs)
    if len(start) == len(ending) == 1 
      return spec(ComposableMorphisms)
    end
  end
  return d # no more specialization possible, it's a FreeGraph
end

end # module
