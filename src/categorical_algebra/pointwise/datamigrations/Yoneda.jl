module Yoneda 
export representable, yoneda, subobject_classifier, internal_hom

using ACSets, GATlab

using .....BasicSets
using ....Cats
using ..Pointwise

# Yoneda embedding
#-----------------

""" Construct a representable C-set.

Recall that a *representable* C-set is one of form ``C(c,-): C → Set`` for some
object ``c ∈ C``.

This function computes the ``c`` representable as the left pushforward data
migration of the singleton ``{c}``-set along the inclusion functor ``{c} ↪ C``,
which works because left Kan extensions take representables to representables
(Mac Lane 1978, Exercise X.3.2). Besides the intrinsic difficulties with
representables (they can be infinite), this function thus inherits any
limitations of our implementation of left pushforward data migrations.
"""
function representable(cons, obname::Symbol; return_unit_id::Bool=false)
  C₀ = Presentation{Symbol}(FreeSchema)
  S = acset_schema(cons())
  C = Presentation(cons())
  add_generator!(C₀, C[obname])
  X = AnonACSet(C₀); add_part!(X, obname)
  F = FinFunctor(Dict(C[obname] => C[obname]), Dict(), FinCat(C₀), FinCat(C))

  typeof(cons().parts[obname]) == IntParts || error(
    "Currently can only compute representables of DenseACSets")
  cat = ACSetCategory(VarACSetCat(X))

  ΣF = SigmaMigrationFunctor(F, X, cons)
  if return_unit_id
    η = ΣF(X; return_unit=true, cat)
    elem = diagram_map(η)[C[obname]] # UNTAG if necessary
    ηob = obname ∈ ob(S) ? elem : untag(elem, S[obname])
    (typeof(cons())(diagram(codom[DiagramIdCat()](η))), only(collect(ηob)))
  else
    ΣF(X; cat)
  end
end

"""
The subobject classifier Ω in a presheaf topos is the presheaf that sends each 
object A to the set of sieves on it (equivalently, the set of subobjects of the 
representable presheaf for A). Counting subobjects gives us the *number* of A 
parts; the hom data for f:A->B for subobject Aᵢ is determined via:

Aᵢ ↪ A 
↑    ↑ f*  
PB⌝↪ B          (PB picks out a subobject of B, up to isomorphism.)

(where A and B are the representables for objects A and B and f* is the unique 
map from B into the A which sends the point of B to f applied to the point of A)

Returns the classifier as well as a dictionary of subobjects corresponding to 
the parts of the classifier.
"""
function subobject_classifier(T::Type; cat=nothing, kw...)
  cat = isnothing(cat) ? infer_acset_cat(T()) : cat
  S = Presentation(T())
  isempty(generators(S, :AttrType)) ||
    error("Cannot compute Ω for schema with attributes")
  y = yoneda(T; kw...)
  obs = generators(S, :Ob)
  subobs = Dict(ob => subobject_graph(ob_map(y, ob))[2] for ob in obs)
  Ω = T()

  for ob in obs
    add_parts!(Ω, nameof(ob), length(subobs[ob]))
  end

  for (f, a, b) in homs(acset_schema(Ω))
    BA = gen_map(y, S[f])
    comp = map(parts(Ω, a)) do pᵢ
      Aᵢ = hom(subobs[S[a]][pᵢ])
      _, PB = force.(pullback[cat](Aᵢ, BA))
      return only(filter(parts(Ω, b)) do pⱼ
        Bⱼ = hom(subobs[S[b]][pⱼ])
        any(σ ->  force(compose[cat](σ, Bⱼ)) == PB, isomorphisms(dom(PB),dom(Bⱼ)))
      end)
    end
    Ω[f] = comp 
  end
  return Ω, subobs
end

"""
Objects: Fᴳ(c) = C-Set(C × G, F)    where C is the representable c

Given a map f: a->b, we compute that f(Aᵢ) = Bⱼ by constructing the following:
          Aᵢ
    A × G → F
  f*↑ ↑ ↑ ↗ Bⱼ       find the hom Bⱼ that makes this commute
    B × G 

where f* is given by `yoneda`.
"""
function internal_hom(G::T, F::T; cat=nothing, kw...) where T<:ACSet
  cat = isnothing(cat) ? infer_acset_cat(G) : cat
  S = Presentation(G)
  y = yoneda(T; kw...)
  obs = generators(S, :Ob)
  prods = Dict(ob => product[cat](ob_map(y, ob),G) for ob in obs)
  maps = Dict(ob => homomorphisms(apex(prods[ob]),F) for ob in obs)
  Fᴳ = T()

  for ob in obs
    add_parts!(Fᴳ, nameof(ob), length(maps[ob]))
  end

  for (f, a, b) in homs(acset_schema(G))
    a, b = S[a], S[b]
    BA = gen_map(y, S[f])
    π₁, π₂ = prods[b]
    Fᴳ[f] = map(parts(Fᴳ, nameof(a))) do pᵢ
      u = universal[cat](prods[a], Span(compose[cat](π₁,BA), π₂))
      composite = force(compose[cat](u, maps[a][pᵢ]))
      findfirst(==(composite), maps[b])
    end
  end

  return Fᴳ, homs
end

""" Compute the Yoneda embedding of a category C in the category of C-sets.

Because Catlab privileges copresheaves (C-sets) over presheaves, this is the
*contravariant* Yoneda embedding, i.e., the embedding functor C^op → C-Set.

The first argument `cons` is a constructor for the ACSet, such as a struct acset
type. If representables have already been computed (which can be expensive),
they can be supplied via the `cache` keyword argument.

Returns a `FinDomFunctor` with domain `op(C)`.
"""
function yoneda(cons; cache::AbstractDict=Dict{Symbol,Any}())
  C = Presentation(cons())

  # Compute any representables that have not already been computed.
  for c in nameof.(generators(C, :Ob))
    haskey(cache, c) && continue
    cache[c] = representable(cons, c, return_unit_id=true)
  end

  for c in nameof.(generators(C, :AttrType))
    haskey(cache, c) && continue
    rep = cons()
    cache[c] = (rep, add_part!(rep, c))
  end

  # Object map of Yoneda embedding.
  y_ob = Dict(C[c] => yc for (c, (yc, _)) in pairs(cache))

  # Morphism map of Yoneda embedding.
  y_hom = Dict(Iterators.map(generators(C, :Hom) ∪ generators(C, :Attr)) do f
    c, d = nameof(dom(f)), nameof(codom(f))
    (yc, rootc), (yd, rootd) = cache[c], cache[d]
    initial = Dict(d => Dict(rootd => yc[rootc,f]))
    f => homomorphism(yd, yc, initial=initial) # Unique homomorphism.
  end)

  FinDomFunctor(y_ob, y_hom, op(FinCat(C)), Category(ACSetCategory(cons())))
end

yoneda(X::DynamicACSet; kw...) = yoneda(constructor(X); kw...)

end # module