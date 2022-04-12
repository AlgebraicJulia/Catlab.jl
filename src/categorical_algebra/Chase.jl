module Chase
export ED, chase, chase_crel, chase_step, to_c_rel, from_c_rel, crel_type,
       egd, tgd, collage, pres_to_eds, pres_to_cset, extend_morphism

using ...Theories, ...Present
using ..CSets
using ..FinSets
using ..FinCats
using ..Limits
using ..FreeDiagrams
import ...Theories: dom, codom
import ..Limits: universal

using Reexport
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
struct ED{Ob,Hom}
  ST :: Hom#ACSetTransformation
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
tgd(e::ED) = factorize(coimage(e.ST), e.ST)
no_change(f) = is_isomorphic(dom(f), codom(f)) # id up to isomorphism

"""Split a list of EDs into two lists of EGDs and TGDs"""
function split_Σ(Σ::Dict{Symbol,ED{Ob,Hom}}
                )::Pair{Dict{Symbol, Hom},Dict{Symbol, Hom}} where {Ob,Hom}
  egds, tgds = [Dict{Symbol, Hom}() for _ in 1:2]
  for (k, ed) in collect(Σ)
    e, t = egd(ed), tgd(ed)
    if !no_change(e)
      egds[k] = e
    end
    if !no_change(t)
      tgds[k] = t
    end
  end
  egds => tgds
end

"""
A collage of a functor is a schema encoding the data of the functor
It has the mapping data in addition to injections from the (co)domain.
"""
function collage(F::FinFunctor)
  (dF, _) = Xs = [dom(F), codom(F)]
  C = coproduct(Xs)
  p = presentation(apex(C)) # inherit equations from dom and codom
  # Add natural transformations
  α = Dict(map(ob_generators(dF)) do o
      o => add_generator!(p, Hom(Symbol("α_$o"), o, ob_map(F, o)))
  end)
  # Add naturality squares
  for f in hom_generators(dF)
    add_equation!(p, compose(α[dom(dF,f)], hom_map(F,f)),
                     compose(f, α[codom(dF,f)]))
  end

  new_codom = FinCat(p)
  ls = map(legs(C)) do l
    FinFunctor(l.ob_map, l.hom_map, dom(l), new_codom)
  end
  Colimit(DiscreteDiagram(Xs), Multicospan(ls))
end

"""
Create constraints for enforcing a C-Set schema on a C-Rel instance.

A presentation implies constraints of foreign keys being functional
(total and unique) in addition to any extra equations.
"""
function pres_to_eds(S::Presentation, name_::Symbol)
  crt = crel_type(S, name_)
  # Convert equations in presentation in EDs
  eds = Dict{String, ACSetTransformation}(
      map(enumerate(equations(S))) do (eqnum, (e1,e2))
    d, cd = Symbol.([dom(e1), codom(e1)])
    l, r1, r2 = [Base.invokelatest(crt) for _ in 1:3]
    add_part!(l, d)
    end1 = add_term!(l, e1)
    end2 = add_term!(l, e2)
    add_part!(r1, cd)
    add_parts!(r2, cd, 2)
    rr = homomorphism(r2, r1)
    rl = ACSetTransformation(r2, l; Dict([cd => [end1,end2]])...)
    "Eq$eqnum" => first(legs(pushout(rl, rr)))
  end)

  # morphisms are functional
  for f_ in S.generators[:Hom]
    d, f, cd = Symbol.([dom(f_), f_, codom(f_)])
    sf, tf = add_srctgt(Symbol(f))
    unique_l, unique_r, total_l = [Base.invokelatest(crt) for _ in 1:3]
    # uniqueness: [d d ⟶ cd] ==> [d ⟶ cd]
    ld = add_part!(unique_l, d); lcd = add_parts!(unique_l, cd, 2)
    add_parts!(unique_l, f, 2; Dict([sf=>[ld], tf=>collect(lcd)])...);
    rd1 = add_part!(unique_r, d); rcd1 = add_part!(unique_r, cd)
    add_part!(unique_r, f; Dict([sf=>rd1, tf=>rcd1])...);
    if d == cd
      uni = ACSetTransformation(unique_l, unique_r;
                                Dict(f=>[1,1], d=>[rd1, rcd1, rcd1])...)
      eds["$(f_)_uni"] = uni
    else
      eds["$(f_)_uni"] = homomorphism(unique_l, unique_r;)
    end
    # totality: [d] ==> [d ⟶ cd]
    add_part!(total_l, d)
    tot = ACSetTransformation(total_l, unique_r; Dict(d=>[rd1])...)
    eds["$(f_)_total"] = tot
  end

  Dict([Symbol(k) => ED{crt, ACSetTransformation}(v) for (k,v) in collect(eds)])
end

"""
Modify C-Set representing a pattern to add a term. Assumes morphism begins from
index 1.
"""
function add_term!(t::StructACSet, args::Vector)
  i = 1
  for fk in args
    d, f, cd = Symbol.([dom(fk), fk, codom(fk)])
    fsrc, ftgt = add_srctgt(f)
    new_i = add_part!(t, cd)
    add_part!(t, f; Dict([fsrc=>i, ftgt=>new_i])...)
    i = new_i
  end
  return i
end

add_term!(t::StructACSet, p::HomExpr{:compose}) = add_term!(t, p.args)
add_term!(t::StructACSet, g::HomExpr{:generator}) = add_term!(t, [g])
add_term!(t::StructACSet,  ::HomExpr{:id}) = add_term!(t, [])

"""
Convert a Presentation to a CSet type. Note this would be improved with
dynamic ACSets.
"""
function pres_to_cset(pres::Presentation, name_::Symbol)
  edges = Symbol.(pres.generators[:Hom])
  expr = CSetDataStructures.struct_acset(name_, StructACSet, pres, index=edges)
  eval(expr)
  return eval(name_)
end


# C-Rel: note that (Span-C)-Set is our model for C-Rel
######################################################

# Convention for the names of span morphisms
add_srctgt(m) = Symbol("src_$m") => Symbol("tgt_$m")

"""    crel_type(x::StructACSet{S}) where S

Convert an instance of a C-Set into an Span(C)-Set type.
"""
function crel_type(x::StructACSet{S}) where S
  crel_type(Presentation(S), typeof(x).name.name)
end

function crel_type(S::Presentation, n::Symbol)
  name_ = Symbol("rel_$n")
  pres = Presentation(FreeSchema)
  edges = vcat(add_srctgt.(Symbol.(S.generators[:Hom]))...)
  xobs = Dict(map([S.generators[:Ob]...,S.generators[:Hom]...]) do s
    s => add_generator!(pres, Ob(FreeSchema, Symbol(s)))
  end)
  for h in S.generators[:Hom]
    hs, ht = dom(h), codom(h)
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
A functor C-Set -> C-Rel, on morphisms. It simply disregards the morphism data
in C-Rel that keeps track of the span apex objects.
"""
function to_c_rel(f::ACSetTransformation)
  d, cd = to_c_rel.([dom(f), codom(f)])
  init = NamedTuple([k => collect(v) for (k, v) in pairs(components(f))])
  homomorphism(d, cd; initial=init)
end


"""    from_c_rel(J::StructACSet,cset::StructACSet{S}) where S

A partial functor C-Rel -> C-Set, on objects.

This fails if a C-Rel morphism is non-unique and returns a C-set with
undefined references if the morphism isn't total (a return flag signals whether
this occured).
"""
function from_c_rel(J::StructACSet,cset::StructACSet{S}) where S
    res = Base.invokelatest(typeof(cset))
    for o in ob(S)
      add_parts!(res, o, nparts(J, o))
    end
    total = true
    for (m, s) in zip(hom(S), dom(S))
      msrc, mtgt = add_srctgt(m)
      length(J[msrc]) == length(Set(J[msrc])) || error("non-unique $J")
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

"""    chase(I::Ob, Σ::Dict{Symbol, ED{Ob,Hom}}, n::Int; verbose=false, viz::Union{Nothing, Function}=nothing) where {Ob, Hom}

Chase a C-Set or C-Rel instance (attributes are tricky - TODO) given a list of
embedded dependencies. This may not terminate, so a bound `n` on the number of
iterations is required.

    [,]
 ΣS  ⟶ Iₙ
⊕↓      ⋮  (resulting morphism)
 ΣT ... Iₙ₊₁

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

TODO this algorithm could be made more efficient by keeping track which EDs have
been searched for over which subobjects, there is no need to search for the same
homomorphism again for an unchanging portion of the instance.
"""
function chase(I::Ob, Σ::Dict{Symbol, ED{Ob,Hom}}, n::Int; verbose=false,
               viz::Union{Nothing, Function}=nothing) where {Ob, Hom}
  Σ_e_t = split_Σ(Σ)
  res = id(I)

  for i in 1:n
    if verbose
      println("\n\nIter $i\n")
      show(stdout,"text/plain",(isnothing(viz) ? identity : viz)(codom(res)))
    end
    next_morphism = chase_step(codom(res), Σ_e_t; verbose=verbose)
    if no_change(next_morphism)
      return res => true
    else
      res = compose(res, next_morphism)
    end
  end
  return res => false # failure
end

"""
`chase` works when both `I` and `Σ` are in C-Set or both are in C-Rel.

This function wraps `chase` and does the necessary conversions (computing in
C-Rel if *either* the initial instance or EDs are provided in C-Rel), returning
a result morphism in C-Set if the chase terminates.
"""
function chase_crel(I::Ob_, Σ::Dict{Symbol,ED{Ob,Hom}}, n::Int;
                    I_is_crel::Bool=false, Σ_is_crel::Bool=false,
                    cset_example::Union{StructACSet,Nothing}=nothing,
                    verbose=false) where {Ob_, Ob, Hom}
  # Process inputs
  is_crel = I_is_crel || Σ_is_crel
  !(is_crel && isnothing(cset_example)) || error("Need CSet for conversion")
  I_rel = (is_crel && !I_is_crel) ? to_c_rel(I) : I
  Σ_rel = (is_crel && !Σ_is_crel) ? to_c_rel.(Σ) : Σ

  # Compute the chase
  viz(x) = from_c_rel(x, cset_example)
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

Optionally initialize the homomorphism search to control the chase process.
"""
function active_triggers(I::Ob, Σ::Dict{Symbol, Hom}; init::Union{NamedTuple, Nothing},
                         verbose::Bool=false) where {Ob, Hom}
  maps = Pair{Hom, Hom}[]
  for (name,ed) in collect(Σ)
    kw = Dict(isnothing(init) ? [] : [:initial=>init])
    for trigger in homomorphisms(dom(ed), I; kw...)
      if isnothing(extend_morphism(trigger, ed))
        if verbose println("\tActive $name") end
        push!(maps, trigger => ed)
      end
    end
  end
  return maps
end

"""
Run a single chase step.
"""
function chase_step(I::Ob, Σ::Pair{Dict{Symbol, Hom},Dict{Symbol, Hom}};
                    init::Union{NamedTuple, Nothing}=nothing,
                    verbose::Bool=false, viz::Union{Function,Nothing}=nothing
                    ) where {Ob,Hom}
    Σegd, Σtgd = Σ

    # First fire one round of TGDs
    ats = active_triggers(I, Σtgd; init=init, verbose=verbose)
    res = isempty(ats) ? id(I) : fire_triggers(ats) # first: fire TGDs
    if !isempty(ats) && verbose
      println("\tPost TGD instance");
      show(stdout,"text/plain",(isnothing(viz) ? identity : viz)(codom(res)))
    end

    # EGDs merely quotient, so this will terminate.
    while true
      if verbose println("\tEGDs") end
      ats = active_triggers(codom(res), Σegd; init=init, verbose=verbose)
      res_ = isempty(ats) ? id(codom(res)) : fire_triggers(ats)
      if force(res_) == force(id(codom(res)))
        return res
      else
        res = compose(res, res_)
      end
    end
    en
end

"""
Compute pushout of all EDs in parallel
"""
function fire_triggers(ats)
  r_i_maps, r_s_maps = first.(ats), last.(ats)
  # Combine each list of morphisms into a single one & take pushout
  I_po = pushout(copair(r_i_maps), oplus(r_s_maps))
  return legs(I_po)[1]
end


"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation,monic=false)::Union{Nothing, ACSetTransformation}

Given a span of morphisms, we seek to find a morphism B → C that makes a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         monic=false, many::Bool=false)
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
  h = many ? homomorphisms : homomorphism
  h(codom(g), codom(f); initial=NamedTuple(init), monic=monic)
end



end # module