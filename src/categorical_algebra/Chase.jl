module Chase
export ED, chase, chase_crel, chase_step, to_c_rel, from_c_rel, crel_type,
       egd, tgd

using Reexport # needed to access struct_acset from CSetDataStructures

using ...Theories, ...Present
using ..CSets
using ..FinSets
using ..Limits
import ...Theories: dom, codom
@reexport using ...CSetDataStructures

# EDs
#####

"""
A morphism S->T, encoding an embedded dependency (or trigger). If the pattern S
is matched (via a homomorphism S->I), we demand there exist a morphism T->I (for
some database instance I) that makes the triangle commute in order to satisfy
the dependency (if this is not the case, then the trigger is 'active').

Homomorphisms can merge elements and introduce new ones. The former kind are
called "equality generating dependencies" (EGDs) and the latter "tuple
generating dependencies" (TGDs). Any homomorphism can be factored into EGD and
TGD components by, respectively, restricting the codomain to the image or
restricting the domain to the coimage.
"""
struct ED
  ST :: ACSetTransformation
end

dom(e::ED) = dom(e.ST)
codom(e::ED) = codom(e.ST)
image(f) = equalizer(legs(pushout(f,f))...)
coimage(f) = coequalizer(legs(pullback(f,f))...)
"""    egd(e::ED)
Distill the component of a morphism that merges elements together
"""
egd(e::ED) = factorize(image(e.ST),e.ST)
"""    tgd(e::ED)
Distill the component of a morphism that adds new elements
"""
tgd(e::ED) = factorize(coimage(e.ST),e.ST)
no_change(f) = is_isomorphic(dom(f), codom(f)) # id up to isomorphism

"""Split a list of EDs into two lists of EGDs and TGDs"""
function split_Σ(Σ::Vector{ED})
  egds, tgds = [],[]
  for ed in Σ
    e, t = egd(ed), tgd(ed)
    if !no_change(e)
      push!(egds, e)
    end
    if !no_change(t)
      push!(tgds, t)
    end
  end
  egds => tgds
end

# C-Rel: note that (Span-C)-Set is our model for C-Rel
######################################################

# Convention for the names of span morphisms
add_srctgt(m) = Symbol("src_$m") => Symbol("tgt_$m")

"""    crel_type(x::StructACSet{S}) where S

Convert an instance of a C-Set into an Span(C)-Set type.
"""
function crel_type(x::StructACSet{S}) where S
  name_ = Symbol("rel_$(typeof(x).name.name)")
  pres = Presentation(FreeSchema)
  edges = vcat(add_srctgt.(hom(S))...)
  xobs = Dict(map([ob(S)...,hom(S)...]) do s
    s => add_generator!(pres, Ob(FreeSchema, s))
  end)
  for (h, hs, ht) in zip(hom(S), dom(S), codom(S))
    s, t = add_srctgt(h)
    add_generator!(pres, Hom(s, xobs[h], xobs[hs]))
    add_generator!(pres, Hom(t, xobs[h], xobs[ht]))
  end
  expr = CSetDataStructures.struct_acset(name_, StructACSet, pres, index=edges)
  eval(expr)
  return eval(name_)
end

"""    to_c_rel(I::StructACSet{S}) where S
A functor C-Set -> C-Rel, on objects. Can be applied safely to C-sets with
undefined references.
"""
function to_c_rel(I::StructACSet{S}) where S
  J = Base.invokelatest(crel_type(I))
  for o in ob(S)
    add_parts!(J, o, nparts(I, o))
  end
  for d in hom(S)
    hs, ht = add_srctgt(d)
    for (i, v) in filter(x->x[2] != 0, collect(enumerate(I[d])))
      n = add_part!(J, d)
      set_subpart!(J, n, hs, i)
      set_subpart!(J, n, ht, v)
    end
  end
  return J
end

"""   to_c_rel(f::ACSetTransformation)
A functor C-Set -> C-Rel, on morphisms
"""
function to_c_rel(f::ACSetTransformation)
  d, cd = to_c_rel.([dom(f), codom(f)])
  init = NamedTuple([k=>collect(v) for (k,v) in pairs(components(f))])
  homomorphism(d, cd; initial=init)
end


"""    from_c_rel(J::StructACSet,cset::StructACSet{S}) where S

A functor C-Rel -> C-Set, on objects.

This fails if a C-rel morphism is noninjective and returns a C-set with
undefined references if the morphism isn't total (a return flag signals whether
this occured).
"""
function from_c_rel(J::StructACSet,cset::StructACSet{S}) where S
    res = typeof(cset)()
    for o in ob(S)
      add_parts!(res, o, nparts(J, o))
    end
    total = true
    for (m, s) in zip(hom(S), dom(S))
      msrc, mtgt = add_srctgt(m)
      length(J[msrc]) == length(Set(J[msrc])) || error("noninjective $J")
      total &= length(J[msrc]) != nparts(J, s)
      for (domval, codomval) in zip(J[msrc], J[mtgt])
        set_subpart!(res, domval, m, codomval)
      end
    end
    return res => total
end

"""    from_c_rel(f::ACSetTransformation,cset::StructACSet{S}) where S

A functor C-Rel -> C-Set, on morphisms.
"""
function from_c_rel(f::ACSetTransformation,cset::StructACSet{S}) where S
  (d, dsucc), (cd, cdsucc) = [from_c_rel(x, cset) for x in [dom(f), codom(f)]]
  comps = Dict([k=>v for (k,v) in pairs(components(f)) if k ∈ ob(S)])
  ACSetTransformation(d, cd; comps...) => (dsucc && cdsucc)
end

# Chase
#######

VPSI = Vector{Pair{Symbol,Int}}

"""    chase(I::StructACSet, Σ::Vector{ED}, n::Int; verbose=false)

Chase a C-Set or C-Rel instance (attributes are tricky - TODO) given a list of
embedded dependencies. This may not terminate, so a bound `n` on the number of
iterations is required.

    [,]
Σ S  ⟶ Iₙ
⊕↓      ⋮  (resulting morphism)
Σ T ... Iₙ₊₁

There is a copy of S and T for each active trigger. A trigger is a map from S
into the current instance. What makes it 'active' is that there is no morphism
from T to I that makes the triangle commute.

Each iteration constructs the above pushout square. The result is a morphism, so
that one can keep track of the provenance of elements in the original CSet
instance within the chased result.

If the initial instance and EDs are all C-sets, then the pushouts can take place
in C-Set (which is more memory efficient). Otherwise, everything is converted to
the Span(C) schema, which is sometimes necessary (for example, migrating data
forward into a cyclic schema).

Whether or not the result is due to success or timeout is returned as a boolean
flag.
"""
function chase(I::StructACSet, Σ::Vector{ED}, n::Int; verbose=false)

  Σ_e_t = split_Σ(Σ)
  res = id(I)

  for i in 1:n
    if verbose println("Iter $i") end
    next_morphism = chase_step(codom(res), Σ_e_t)
    if no_change(next_morphism)
      return res => true
    else
      res = compose(res, next_morphism)
    end
  end
  return res => false # failure
end

"""    chase_crel(I::StructACSet, Σ::Vector{ED}, n::Int; I_is_crel::Bool=false, Σ_is_crel::Bool=false, cset_example::Union{StructACSet,Nothing}=nothing, verbose=false)

`chase` works when both `I` and `Σ` are in C-Set or both are in C-Rel, though in the latter case the return value is a C-Rel morphism rather than one in C-Set.

This function wraps `chase` and does the necessary conversions (computing in
C-Rel if either the initial instance or EDs are provided in C-Rel), returning
a result morphism in C-Set if the chase terminates.
"""
function chase_crel(I::StructACSet, Σ::Vector{ED}, n::Int;
                    I_is_crel::Bool=false, Σ_is_crel::Bool=false,
                    cset_example::Union{StructACSet,Nothing}=nothing, verbose=false)
  # Process inputs
  is_crel = I_is_crel || Σ_is_crel
  !(is_crel && isnothing(cset_example)) || error("Need CSet for conversion")
  I_rel = (is_crel && !I_is_crel) ? to_c_rel(I) : I
  Σ_rel = (is_crel && !Σ_is_crel) ? to_c_rel.(Σ) : Σ

  # Compute the chase
  res, succ = chase(I_rel, Σ_rel, n; verbose=verbose)

  # Postprocess results
  if !succ
    return res => false
  end
  return (is_crel ? from_c_rel(res, cset_example)[1] : res) => true
end

"""
Naively determine active triggers of EDs (S->T) by filtering all triggers
(i.e. maps S->I) to see which are active (i.e. there exists no T->I such that
S->T->I = S->I).

Optionally restrict to only considering a subset of the triggers with `ts`, a
list of indices into the list of triggers.
"""
function active_triggers(I::T_, Σ; init::Union{NamedTuple, Nothing}
          )::Vector{Pair{ACSetTransformation, ACSetTransformation}} where {
                    T_<:StructACSet}
  maps = Pair{ACSetTransformation, ACSetTransformation}[]
  for ed in Σ
    kw = Dict(isnothing(init) ? [] : [:initial=>init])
    for trigger in homomorphisms(dom(ed), I; kw...)
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
function chase_step(I::StructACSet, Σ; init::Union{NamedTuple, Nothing}=nothing)
    Σe, Σt = Σ
    ats = active_triggers(I, Σt; init=init)
    res = isempty(ats) ? id(I) : fire_triggers(ats) # first: fire TGDs
    while true
      ats = active_triggers(codom(res), Σe; init=init)
      res_ = isempty(ats) ? id(codom(res)) : fire_triggers(ats)
      if force(res_) == force(id(codom(res)))
        return res
      else
        res = compose(res, res_)
      end
    end
    en
end

function fire_triggers(ats)
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
