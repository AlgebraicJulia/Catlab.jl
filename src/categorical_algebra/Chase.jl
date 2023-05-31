"""
The chase is an algorithm which subjects a C-Set instance to constraints 
expressed in the language of regular logic, called embedded dependencies 
(EDs, or 'triggers'). 

A morphism S->T, encodes an embedded dependency. If the pattern 
S is matched (via a homomorphism S->I), we demand there exist a morphism T->I 
(for some database instance I) that makes the triangle commute in order to 
satisfy the dependency (if this is not the case, then the trigger is 'active').

Homomorphisms can merge elements and introduce new ones. The former kind are
called "equality generating dependencies" (EGDs) and the latter "tuple
generating dependencies" (TGDs). Any homomorphism can be factored into EGD and
TGD components by, respectively, restricting the codomain to the image or
restricting the domain to the coimage.
"""
module Chase
export chase

using ACSets.DenseACSets: datatypes
using ...Present, ...Theories
using ..CSets, ..FinSets, ..FinCats, ..Limits, ..FreeDiagrams
using ..FinCats: FinCatPresentation
import ..Limits: universal
import ..Categories: ob_map

# EDs
#####

"""Distill the component of a morphism that merges elements together"""
egd(e::CSetTransformation) = factorize(image(e),e)
"""Distill the component of a morphism that adds new elements"""
tgd(e::CSetTransformation) = factorize(coimage(e), e)
"""Check if id up to isomorphism"""
no_change(f) = all(c->is_monic(c) && is_epic(c), components(f))

"""Split a dict of (general) EDs into dicts of EGDs and TGDs"""
split_Σ(Σ::Dict{Symbol,T}) where {S,T<:CSetTransformation{S}} = map([egd, tgd]) do f 
    Dict([k=>f(v) for (k,v) in collect(Σ) if !no_change(f(v))])
end

"""
We do not have general limits for ACSet transformations, so we cannot yet 
automatically factor an ED into an EGD+TGD. However, it should be possible to 
define limits such that the CSetTransformation code above works for ACSets too.
"""
function split_Σ(Σ::Dict{Symbol,<:ACSetTransformation})
  egds, tgds = Dict(), Dict()
  for (k,v) in collect(Σ)
    e, m = is_epic(v), is_monic(v)
    if !e && !m error("Cannot automatically factor ED $v")
    elseif m && !e tgds[k] = v # monic = TGD
    elseif e && !m egds[k] = v # epic = EGD
    end                        # otherwise, no change
  end
  return egds => tgds
end


"""
Create constraints for enforcing a C-Set schema on a C-Rel instance.

A presentation implies constraints of foreign keys being functional
(total and unique) in addition to any extra equations.
"""
function pres_to_eds(S::Presentation; types=Dict(), name="")
  ACS = crel_type(S; types=types, name=name)
  # Convert equations in presentation in EDs
  eds = Dict{String,ACSetTransformation}(["Eq$i" => equation_to_ed(S,ACS,e1,e2)
      for (i, (e1,e2)) in enumerate(equations(S))])

  # morphisms are functional, i.e. unique and total
  for f_ in generators(S,:Hom) ∪  generators(S,:Attr)
    atvar(i) = f_ ∈ generators(S,:Attr) ? AttrVar(i) : i 
    d, f, cd = Symbol.([dom(f_), f_, codom(f_)])
    sf, tf = add_srctgt(Symbol(f))
    unique_l, unique_r, total_l = [ACS() for _ in 1:3]
    # uniqueness: [d d ⟶ cd] ==> [d ⟶ cd]
    ld = add_part!(unique_l, d); lcd = add_parts!(unique_l, cd, 2)
    lcd = atvar.(collect(lcd))
    add_parts!(unique_l, f, 2; Dict([sf=>[ld], tf=>lcd])...);
    rd1 = add_part!(unique_r, d); rcd1 = add_part!(unique_r, cd)
    add_part!(unique_r, f; Dict([sf=>rd1, tf=>atvar(rcd1)])...);
    if d == cd # not possible if f is an attribute
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

  return Dict([Symbol(k) => v for (k,v) in collect(eds)])
end

"""
An equation is a pair of paths: 
     ↗ a₁ → ... → aₙ
start 
     ↘ b₁ → ... → bₙ

The EGD that enforces the equation has, as domain a CSet whose category of 
elements looks like the above graphic. Its codomain is the same, with aₙ and bₙ
merged. This merging is performed via a pushout. The diagram above corresponds 
to `l`, while `r1` is a single point of type aₙ. `r2` has two points of that 
type, with a unique map to `r1` and picking out `aₙ` and `bₙ` in its map into 
`l`.
"""
function equation_to_ed(S,ACS,e1,e2)
  d, cd = Symbol.([dom(e1), codom(e1)])
  l, r1, r2 = [ACS() for _ in 1:3]
  add_part!(l, d)
  end1 = add_term!(l, e1)
  end2 = add_term!(l, e2)
  add_part!(r1, cd)
  add_parts!(r2, cd, 2)
  is_attr = cd ∈ Symbol.(generators(S,:AttrType))
  rrcomps = Dict(cd=>(is_attr ? AttrVar : identity).([1,1]))
  rr = ACSetTransformation(r2, r1; rrcomps...)
  rl = ACSetTransformation(r2, l; Dict([cd => [end1,end2]])...)
  return first(legs(pushout(rl, rr)))
end

"""
Modify C-Set representing a pattern to add a term. Assumes morphism begins from
index 1.
"""
function add_term!(t::ACSet, args::Vector)
  S = acset_schema(t)
  i = 1
  for fk in args
    _, f, cd = Symbol.([dom(fk), fk, codom(fk)])
    is_attr(i) = cd ∈ attrtypes(S) ? AttrVar(i) : i
    fsrc, ftgt = add_srctgt(f)
    new_i = is_attr(add_part!(t, cd))
    add_part!(t, f; Dict([fsrc=>i, ftgt=>new_i])...)
    i = new_i
  end
  return i
end

add_term!(t::ACSet, p::HomExpr{:compose}) = add_term!(t, p.args)
add_term!(t::ACSet, p::FreeSchema.Attr{:compose}) = add_term!(t, p.args)
add_term!(t::ACSet, g::HomExpr{:generator}) = add_term!(t, [g])
add_term!(t::ACSet, g::FreeSchema.Attr{:generator}) = add_term!(t, [g])
add_term!(t::ACSet,  ::HomExpr{:id}) = add_term!(t, [])


# C-Rel: note that (Span-C)-Set is our model for C-Rel
######################################################

# Naming convention for the names of span morphisms
add_srctgt(m) = Symbol("src_$m") => Symbol("tgt_$m")

"""
Create an ACSet type that replaces each Hom/Attr with a span.
If a name is provided, return a ()->DynamicACSet, otherwise an AnonACSetType.
"""
function crel_type(S::Presentation; types=Dict(), name="")
  pres = Presentation(FreeSchema)
  xobs = merge(Dict(map(vcat([generators(S,x) for x in [:Ob,:Hom,:Attr]]...)) do s
    Symbol(s) => add_generator!(pres, Ob(FreeSchema, Symbol(s)))
  end), Dict([o=>add_generator!(pres,AttrType(FreeSchema.AttrType, o)) 
             for o in Symbol.(generators(S,:AttrType))]))
  for h in generators(S,:Hom)
    hs, ht = Symbol.([dom(h), codom(h)])
    s, t = add_srctgt(h)
    add_generator!(pres, Hom(s, xobs[Symbol(h)], xobs[hs]))
    add_generator!(pres, Hom(t, xobs[Symbol(h)], xobs[ht]))
  end
  for h in generators(S, :Attr)
    hs, ht = Symbol.([dom(h), codom(h)])
    s, t = add_srctgt(h)
    add_generator!(pres, Hom(s, xobs[Symbol(h)], xobs[hs]))
    add_generator!(pres, Attr(t, xobs[Symbol(h)], xobs[ht]))
  end
  if isempty(name)    # AnonACSetType gives an error, unexpectedly
    return AnonACSet(pres, type_assignment=Dict{Symbol,Type}(types)) |> typeof
  else 
    return () -> DynamicACSet(name, pres; type_assignment=types)
  end
end

"""
A functor C-Set -> C-Rel, on objects. Can be applied safely to C-sets with
undefined references.
"""
function to_c_rel(I::StructACSet{S, Ts}) where {S,Ts}
  J = crel_type(Presentation(S); types=datatypes(I))()
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

"""
A functor C-Set -> C-Rel, on morphisms. It simply disregards the morphism data
in C-Rel that keeps track of the span apex objects.
"""
function to_c_rel(f::ACSetTransformation)
  d, cd = to_c_rel.([dom(f), codom(f)])
  init = NamedTuple([k => collect(v) for (k, v) in pairs(components(f))])
  homomorphism(d, cd; initial=init)
end

"""
A partially defined inverse to to_c_rel.

This fails if a C-Rel morphism is non-unique and returns a C-set with
undefined references if the morphism isn't total (a return flag signals whether
this occured).
"""
function from_c_rel(J::ACSet,cset::ACSet) 
    S = acset_schema(cset)
    res = typeof(cset)()
    for o in ob(S)
      add_parts!(res, o, nparts(J, o))
    end
    total = true
    for (m, s, _) in homs(S)
      msrc, mtgt = add_srctgt(m)
      length(J[msrc]) == length(Set(J[msrc])) || error("non-unique $J")
      total &= length(J[msrc]) != nparts(J, s)
      for (domval, codomval) in zip(J[msrc], J[mtgt])
        set_subpart!(res, domval, m, codomval)
      end
    end
    return res => total
end

"""A partially defined inverse to to_c_rel., on morphisms."""
function from_c_rel(f::ACSetTransformation,cset::StructACSet{S}) where S
  (d, dsucc), (cd, cdsucc) = [from_c_rel(x, cset) for x in [dom(f), codom(f)]]
  comps = Dict([k=>v for (k,v) in pairs(components(f)) if k ∈ ob(S)])
  ACSetTransformation(d, cd; comps...) => (dsucc && cdsucc)
end

# Chase
#######

"""    chase(I::ACSet, Σ::AbstractDict, n::Int)

Chase a C-Set or C-Rel instance given a list of
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

Whether or not the result is due to success or timeout is returned as a boolean
flag.

TODO: this algorithm could be made more efficient by homomorphism caching.
"""
function chase(I::ACSet, Σ::AbstractDict, n::Int)
  Σ_egd, Σ_tgd = split_Σ(Σ)
  res = id(I) # initialize result
  for i in 1:n
    @debug "Chase iteration $i" result = codom(res)
    next_morphism = chase_step(codom(res), Σ_egd, Σ_tgd)
    if no_change(next_morphism)
      return res => true
    else
      res = compose(res, next_morphism)
    end
  end
  return res => false # failure
end

"""
Naively determine active triggers of EDs (S->T) by filtering all triggers
(i.e. maps S->I) to see which are active (i.e. there exists no T->I such that
S->T->I = S->I). Store the trigger with the ED as a span, I<-S->T.

Optionally initialize the homomorphism search to control the chase process.
"""
function active_triggers(I::ACSet, Σ::AbstractDict; 
                         init::Union{NamedTuple, Nothing})
  maps = Span[]
  @debug "Looking for active triggers"
  for (name,ed) in collect(Σ)
    @debug "Checking if trigger $name is active"
    kw = Dict(isnothing(init) ? [] : [:initial=>init])
    for trigger in homomorphisms(dom(ed), I; kw...)
      if isnothing(extend_morphism(trigger, ed))
        @debug "Active $name"
        push!(maps, Span(trigger, ed))
      end
    end
  end
  @debug "Found $(length(maps)) active triggers"
  return maps
end

"""Run a single chase step."""
function chase_step(I::ACSet, Σegd, Σtgd; init::Union{NamedTuple, Nothing}=nothing)
  # First fire one round of TGDs
  ats = active_triggers(I, Σtgd; init=init)
  res = isempty(ats) ? id(I) : fire_triggers(ats) # first: fire TGDs
  if !isempty(ats)
    @debug "Post TGD instance" result = codom(res)
  end

  # EGDs merely quotient, so this will terminate.
  while true
    ats = active_triggers(codom(res), Σegd; init=init)
    res_ = isempty(ats) ? id(codom(res)) : fire_triggers(ats)
    if force(res_) == force(id(codom(res)))
      return res
    else
      res = compose(res, res_)
    end
  end
end

"""
Compute pushout of all EDs in parallel by combining each list of morphisms into 
a single one & taking a pushout.
"""
function fire_triggers(ats)
  r_i_maps, r_s_maps = left.(ats), right.(ats)
  I_po = pushout(copair(r_i_maps), oplus(r_s_maps))
  return legs(I_po)[1]
end

# Sigma migration
#################

"""
A collage of a functor is a schema encoding the data of the functor
It has the mapping data in addition to injections from the (co)domain.
"""
function collage(F::FinFunctor)
  (dF, _) = Xs = [dom(F), codom(F)]
  C = coproduct_fincat(Xs)
  i1, i2 = legs(C)
  p = presentation(apex(C)) # inherit equations from dom and codom
  # Add natural transformations
  α = Dict(map(ob_generators(dF)) do o
    o => add_generator!(p, Hom(Symbol("α_$o"), ob_map(i1,o), ob_map(i2,ob_map(F, o))))
  end)
  # Add naturality squares
  for f in hom_generators(dF)
    add_equation!(p, compose(α[dom(dF,f)], i2(hom_map(F,f))),
                     compose(i1(f),        α[codom(dF,f)]))
  end
  new_codom = FinCat(p)
  ls = map(legs(C)) do l
    FinFunctor(l.ob_map, l.hom_map, dom(l), new_codom)
  end
  Colimit(DiscreteDiagram(Xs), Multicospan(ls)) => p
end


# Extending morphisms (should this be in CSets.jl)
##################################################
"""
Given a span of morphisms, we seek to find a morphism B → C that makes a
commuting triangle if possible.
Accepts homomorphism search keyword arguments to constrain the Hom(B,C) search.
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
    initial=Dict(), kw...)::Union{Nothing, ACSetTransformation}
  init = combine_dicts!(extend_morphism_constraints(f,g), initial)
  isnothing(init) ? nothing : homomorphism(codom(g), codom(f); initial=init, kw...)
end

"""
Given a span of morphisms, we seek to find all morphisms B → C that make a
commuting triangle.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
This may be impossible, because f(a₁)≠f(a₂) but g(a₁)=g(a₂), in which case 
return `nothing`. Otherwise, return a Dict which can be used to initialize the 
homomorphism search Hom(B,C).
"""
function extend_morphism_constraints(f::ACSetTransformation,
                                     g::ACSetTransformation) 
  dom(f) == dom(g) || error("f and g are not a span: $f \n$g")
  S = acset_schema(dom(f))
  init = Dict() # {Symbol, Dict{Int,Int}}
  for (ob, mapping) in pairs(components(f))
    init_comp = [] # Pair{Int,Int}
    is_var = ob ∈ attrtypes(S)
    for i in parts(codom(g), ob)
      p = preimage(g[ob], is_var ? AttrVar(i) : i )
      vs = Set(mapping.(is_var ? AttrVar.(p) : p))
      if length(vs) == 1
        push!(init_comp, i => only(vs))
      elseif length(vs) > 1 # no homomorphism possible
        return nothing
      end
    end
    init[ob] = Dict(init_comp)
  end
  return init
end

 
"""
Combine a user-specified initial dict with `init`, generated by constraints
`Initial` could contain vectors or int-keyed dicts as its data for each object.  
"""
function combine_dicts!(init, initial)
  if isnothing(init) return nothing end
  for (k,vs) in collect(initial)
    for (i, v) in (vs isa AbstractVector ? enumerate : collect)(vs)
      if haskey(init[k], i)
        if init[k][i] != v return nothing end 
      else 
        init[k][i]  = v 
      end
    end
  end
  return NamedTuple(init)
end 

# Colimit of ACset FinCats
##########################
"""
Preserves the original name of the inputs if it is unambiguous, otherwise
disambiguates with index in original input. E.g. (A,B)⊔(B,C) → (A,B#1,B#2,C)
"""
function coproduct_fincat(Xs::AbstractVector{<: FinCatPresentation{ThSchema}}; kw...)
  Xps = [X.presentation for X in Xs]
  # Collect all generators and identify conflicting names
  cnflobs, cnflats, cnflhoms, cnflattrs = map([:Ob,:AttrType,:Hom,:Attr]) do x 
    all_ob = Symbol.(vcat([generators(X,x) for X in Xps]...))
    Set([i for i in all_ob if count(==(i), all_ob) > 1])
  end
  # Create new disjoint union presentation
  p = Presentation(FreeSchema)
  ogens = Dict(vcat(map(enumerate(Xps)) do (i, X)
    map(Symbol.(generators(X,:Ob))) do o
      (i,o) => Ob(FreeSchema, Symbol("$o" * (o ∈ cnflobs ? "#$i" : "")))
    end
  end...))
  map(values(ogens)) do g add_generator!(p, g) end

  agens = Dict(vcat(map(enumerate(Xps)) do (i, X)
    map(Symbol.(generators(X,:AttrType))) do o
      (i,o) => AttrType(FreeSchema.AttrType, Symbol("$o" * (o ∈ cnflats ? "#$i" : "")))
    end
  end...))
  map(values(agens)) do g add_generator!(p, g) end
  gens = merge(ogens,agens)

  hgens = Dict(vcat(map(enumerate(Xs)) do (i, X)
    map(generators(X.presentation,:Hom)) do h
      n = Symbol("$h" * (Symbol(h) ∈ cnflhoms ? "#$i" : ""))
      d, cd = Symbol.([dom(X,h), codom(X,h)])
      s, t = gens[(i, Symbol(d))], gens[(i, Symbol(cd))]
      (i,Symbol(h)) => Symbol(add_generator!(p, Hom(n, s, t)))
    end
  end...))

  atgens = Dict(vcat(map(enumerate(Xs)) do (i, X)
    map(generators(X.presentation,:Attr)) do h
      n = Symbol("$h" * (Symbol(h) ∈ cnflattrs ? "#$i" : ""))
      d, cd = Symbol.([dom(X,h), codom(X,h)])
      s, t = gens[(i, Symbol(d))], gens[(i, Symbol(cd))]
      (i,Symbol(h)) => Symbol(add_generator!(p, Attr(n, s, t)))
    end
  end...))

  gens′ = merge(hgens, atgens)

  # Create legs into equationless target to help us project the equations
  for (i,x) in enumerate(Xs)
    os, hs = map(zip([ob_generators,hom_generators], [gens,gens′])) do (get, g)
      Dict([o => Symbol(g[(i,o)]) for o in Symbol.(get(x))])
    end
    l = FinDomFunctor(os, hs, x, FinCat(p))
    for (e1,e2) in equations(x)
      add_equation!(p, hom_map(l, e1), hom_map(l, e2))
    end
  end

  # Create legs into equationful target
  ls = map(enumerate(Xs)) do (i,x)
    os, hs = map(zip([ob_generators,hom_generators], [gens,gens′])) do (get, g)
      Dict([o => g[(i,o)] for o in Symbol.(get(x))])
    end
    FinDomFunctor(os, hs, x, FinCat(p))
  end

  Colimit(DiscreteDiagram(Xs), Multicospan(ls))
end

end # module
