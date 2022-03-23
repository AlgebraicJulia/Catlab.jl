module Chase
export ED, chase, chase_step, active_triggers

using ...Theories
using ..CSets
using ..FinSets
using ..Limits
import ...Theories: dom, codom

"""
A morphism S->T, encoding an embedded dependency. If the pattern S is matched
(via a homomorphism S->I), we demand there exist a morphism T->I that makes the
triangle commute.
"""
struct ED
  ST :: ACSetTransformation
end

dom(e::ED) = dom(e.ST)
codom(e::ED) = codom(e.ST)


VPSI = Vector{Pair{Symbol,Int}}
"""
Chase a CSet instance (attributes are tricky - TODO) given a list of embedded
dependencies. This may not terminate, so a bound on the number of iterations is
required.

    [,]
Σ S  ⟶ Iₙ
⊕↓      ⋮  (resulting morphism)
Σ T ... Iₙ₊₁

There is a copy of S and T for each active trigger. A trigger is a map from S
into the current instance. What makes it 'active' is that there is no morphism
from T to I that makes the triangle commute.

Each iteration constructs the above pushout square. The result is a morphism so
that one can keep track of the provenance of elements in the original CSet instance within
the chased result.

Also eturns whether or not the result is due to success or timeout.
"""
function chase(I::StructACSet, Σ::Vector{ED}, n::Int; verbose=false)
  res = id(I)
  for i in 1:n
    if verbose println("Iter $i") end
    next_morphism = chase_step(codom(res), Σ)
    if isnothing(next_morphism)
      return res => true # success
    else
      res = compose(res, next_morphism)
    end
  end
  return res => false # failure
end

"""
Naively determine active triggers of EDs (S->T) by filtering all triggers
(i.e. maps S->I) to see which are active (i.e. there exists no T->I such that
S->T->I = S->I).

Optionally restrict to only considering a subset of the triggers with `ts`, a
list of indices into the list of triggers.
"""
function active_triggers(I::T_, Σ::Vector{ED}; ts::Vector{Int}=Int[]
                  )::Vector{Pair{ACSetTransformation, ACSetTransformation}} where {
                    T_<:StructACSet}
  maps = Pair{ACSetTransformation, ACSetTransformation}[]
  for ed_ in Σ
    ed = ed_.ST
    for trigger in last.(filter(ih->isempty(ts) || ih[1] in ts,
                                collect(enumerate(homomorphisms(dom(ed), I)))))
      if isnothing(extend_morphism(trigger, ed))
        push!(maps, trigger => ed)
      end
    end
  end
  return maps
end

"""
Run a single chase step. Optionally select a subset of triggers to fire on.
This selection could be generalized to be a function which does a computation
to determine which firings are useful.
"""
function chase_step(I::StructACSet, Σ::Vector{ED}; ts::Vector{Int}=Int[])
    ats = active_triggers(I, Σ; ts=ts)
    if isempty(ats)  # Early termination condition
      return I, ins, outs
    end
    r_i_maps, r_s_maps = first.(ats), last.(ats)
    # Combine each list of morphisms into a single one & take pushout
    I_po = pushout(copair(r_i_maps), oplus(r_s_maps))
    # Propagate info about which vertices are inputs/outputs & update I
    return legs(I_po)[1]
end


"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation)::Union{Nothing, ACSetTransformation}
Given a span of morphisms, we seek to find a morphism B → C that makes a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         monic=false)::Union{Nothing, ACSetTransformation}
  dom(f) == dom(g) || error("f and g are not a span: $jf \n$jg")

  init = Dict{Symbol, Dict{Int,Int}}()
  for (ob, mapping) in pairs(components(f))
    init_comp = Pair{Int,Int}[]
    for i in parts(codom(g), ob)
      vs = Set(mapping(preimage(g[ob], i)))
      if length(vs) == 1
        push!(init_comp, i => only(vs))
      elseif length(vs) > 1 # no homomorphism possible
        return nothing
      end
    end
    init[ob] = Dict(init_comp)
  end
  homomorphism(codom(g), codom(f); initial=NamedTuple(init), monic=monic)
end


end # module