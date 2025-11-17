module Yoneda 
export representable, yoneda, subobject_classifier, internal_hom, @acset_colim, 
  @named_acset_colim, @acset_transformation_colim

using DataStructures, MLStyle 

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


# ACSet colim 
##############

# A representable + a map out of it
const RPath = Pair{Symbol, Vector{Symbol}}

# An equation given by two RPaths
const REq = Pair{RPath, RPath}

"""
Parse the data from the `@acset_colim` user input 

- `reprs` is keyed by the ob/attrtypes and sends each to a set of symbols which 
   are names for the representables.
- `eqs` contains equations of the form f(x) = g(y) where x,y are reprs and f 
   and g are morphisms
- `vals` identifies certain representable attribute variables with Julia values
"""
struct DiagramData 
  reprs::AbstractDict{Symbol, Set{Symbol}}
  eqs::Vector{REq}
  vals::Dict{RPath, Any}
  DiagramData() = new(DefaultDict{Symbol, Set{Symbol}}(()->Set{Symbol}()),
                      REq[], Dict{RPath, Any}())
end

function parse_diagram_data(x::Expr, mod::Module)::DiagramData
  data = DiagramData()
  x.head == :block || error("Expected block expression, not $x")

  function add_part(partname::Symbol,parttype::Symbol) 
    any(values(data.reprs)) do vs 
      partname ∈ vs && error("Duplicate part name $partname")
    end
    push!(data.reprs[parttype], partname)
  end

  parse_call(e::Symbol)::RPath = e => Symbol[]

  parse_call(e::Expr) = @match e begin
    Expr(:call, f, x) => let (e, fs) = parse_call(x);
      e => [f; fs]
    end
    Expr(:$, x) => Base.eval(mod, x)
  end

  function parse_eq(t1t2::Tuple) 
    p1,p2 = parse_call.(t1t2)
    if p1 isa RPath
      if p2 isa RPath 
        push!(data.eqs, p1 => p2) 
      else 
        data.vals[p1] = p2
      end 
    else
      data.vals[p2] = p1
    end
  end

  for arg in Base.remove_linenums!(x).args
    @match arg begin
      Expr(:(::), partname::Symbol, parttype::Symbol) => begin 
        add_part(partname, parttype)
      end
      Expr(:(::), Expr(:tuple, partnames...), parttype::Symbol) => begin
        add_part.(partnames, Ref(parttype))
      end
      Expr(:call, :(==), t1, t2) => parse_eq((t1,t2))
      Expr(:comparison, raw...) => begin
        all(==(:(==)), raw[2:2:end]) || error("Improper equality $arg")
        ts = raw[1:2:end]
        parse_eq.(zip(ts, ts[2:end]))
      end
      _ => error("Unexpected expr $arg")
    end
  end
  data
end

"""
Uses the output of `yoneda`:

```
@acset_colim yGraph begin 
  (e1,e2)::E 
  src(e1) == tgt(e2) 
end
```
"""
macro acset_colim(yon, body)
  quote 
    colimit_representables($(parse_diagram_data(body, __module__)), $(esc(yon)))[2]
  end
end

"""
```
Dom = @named_acset_colim yGraph MyDomain begin
  v::V; e::E; src(e)==v
end
```

This would be have like `@acset_colim` and assign to `Dom` the walking edge 
ACSet with src=1 and tgt=2. However, unlike `@acset_colim`, this also assigns 
to a variable MyDomain the NamedTuple `(v=(:V, 1),e=(:E, 1))`.
"""
macro named_acset_colim(yon, names_var, body)
  quote 
    names, acset = colimit_representables($(parse_diagram_data(body, __module__)), $(esc(yon)))
    $(esc(names_var)) = names
    acset
  end
end

"""
Although providing an assignment for every generator is sufficient to guarantee
a uniquely determined homomorphism, it is not always necessary. If a generator
`a` in the domain is equal to some `b.f`, then only specifying `b` is necessary.
Furthermore, keyword arguments like `monic`, `epic`, and `iso` can be used to
specify a morphism uniquely (or `any` + `random` if it doesn't matter).
"""
macro acset_transformation_colim(yon, body1, body2, body3, kwargs=:((;)))
    initial = Dict(map(filter(e->e isa Expr,body3.args)) do e 
      @match e begin 
        Expr(:call, :(=>), a, b) => a => b
      end
    end)
    quote 
    names1, acset1 = colimit_representables(
      $(parse_diagram_data(body1, __module__)), $(esc(yon)))
    names2, acset2 = colimit_representables(
      $(parse_diagram_data(body2, __module__)), $(esc(yon)))

    initial=DefaultDict{Symbol,Dict}(()->Dict())
    for (k,v) in $initial 
      ty, domval = names1[k]
      _, codval = names2[v]
      initial[ty][domval] = codval
    end
    homomorphism(acset1, acset2; initial=initial, $(kwargs)...)
  end
end


""" 
Construct an ACSet given a colimit of representables, given by generating 
representables and relations. Assumes a background context of VarACSetCategory
"""
function colimit_representables(data::DiagramData, y::FinDomFunctor)
  # Warning: we assume FinDomFunctor is implemented by FinDomFunctorMap to
  # get access to an arbitrary element (not part of the FinCat interface)
  arb = last(first(getvalue(y).ob_map))
  S = acset_schema(arb)
  P = Presentation(S)
  
  gen(x) = generator(P, x)

  ks = collect(keys(data.reprs))

  𝒞 = ACSetCategory(VarACSetCat(arb))
  𝒞′ = TypedCatWithCoproducts(𝒞)

  # Total order on the representables 
  reprs = []
  for (k, vs) in data.reprs, v in vs
    push!(reprs, (k, v))
  end

  # Construct a coproduct of all representables
  representable_csets = ob_map.(Ref(y), gen.(first.(reprs)))
  Σ = coproduct[𝒞](representable_csets...)
  ι = legs(Σ) # the i'th inclusion leg identifies the ith repr in the coproduct

  # Given a name of some representable, get its corresponding inclusion into Σ
  lookup = Dict([v=>ι[i] for (i,(_,v)) in enumerate(reprs)])

  # Convert a morphism out of a representable into an ACSetTransformation into Σ
  function list_to_hom(rep_f::RPath)::ACSetTransformation
    rep, f = rep_f
    p = if isempty(f)
      k = ks[findfirst(k->rep ∈ data.reprs[k], ks)]
      id(gen(k))
    else
      compose(gen.(f))
    end
    m = @match only(typeof(p).parameters) begin 
      :generator => gen_map(y, p) 
      :compose => hom_map(y, p)
      :id => id[𝒞](ob_map(y, dom(p)))
    end
    compose[𝒞](m, lookup[rep])
  end

  # A quotient for each equation: if we are identifying a rep x, this is a span 
  # x ⇇ x² ⇉ Σᵢrᵢ where the left is merge + the right map comes from an equation
  spans = map(data.eqs) do lr
    l, r = map(list_to_hom,lr)
    merge = let idᵣ = id[𝒞](dom(l)); copair[𝒞′](idᵣ,idᵣ) end
    Span(merge, copair[𝒞′](l,r))
  end

  # A quotient for each fixed value: assert the attrvar is equal via pushout
  for (rp,val) in pairs(data.vals)
    h = list_to_hom(rp)
    T = codom(S, last(last(rp))) 
    set_val = ACSetTransformation(ob_map(y, gen(T)), constructor(𝒞); 
                                  Dict([T=>[val]])...)
    push!(spans, Span(set_val, h))
  end

  # If we are just asking for a coproduct of representables
  isempty(spans) && return (names, apex(Σ))

  # Perform all pushouts at once by putting the spans together in parallel
  lefts, rights = left.(spans), right.(spans)
  _,bigι = big_colim = pushout[𝒞](foldl(oplus[𝒞′], lefts), foldl(copair[𝒞′], rights))

  # TODO get representing element for real. Requires passing in extra data.
  names = NamedTuple(map(reprs) do (repr_type, repr_name)
    ι = FinFunction(lookup[repr_name][repr_type], bigι[repr_type])
    length(dom(ι)) == 1 || error("Assumption that representing element is "*
    "unique has been violated, more data required by `colimit_representables`")
    repr_name => (repr_type, ι(only(dom(ι))))
  end) 

  (names, apex(big_colim))
end

end # module
