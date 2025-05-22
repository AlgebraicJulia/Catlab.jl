export FinFunctor, FinDomFunctor, is_functorial, functoriality_failures, 
       FinDomFunctor′, is_initial, 
       collect_ob, collect_hom, make_map, components, gen_map,
       ThFinDomFunctor, force, mapvals, dom_cat, codom_cat, mappairs,
       FunctorFinDom, FinFunctorAsFunctor, compose_abs_functor

using DataStructures: IntDisjointSets, in_same_set, num_groups
using StructEquality

using GATlab, ACSets

import ....Theories: dom, codom
using ....Graphs
import ....BasicSets: force
using ..Categories, ..FinCats, ..Functors
import ..Functors: ob_map, hom_map, show_type_constructor, validate
import ..FreeDiagrams: FreeDiagram, FreeGraph
using ..Paths: Path

# Dict utilities
################

# Something like this should be built into Julia, but unfortunately isn't.

"""
Map two given functions across the respective keys and values of a dictionary.
"""
function mappairs(kmap, vmap, pairs::T;fixkeytype=false,fixvaltype=false) where {K,V,T<:AbstractDict{K,V}}
  S = dicttype(T)
  d = S(kmap(k) => vmap(v) for (k,v) in pairs)
  R = fixvaltype ? fixkeytype ? T : S{keytype(d),V} :
      fixkeytype ? S{K} : S
  R(d)
end
#XX:might want to add fixtype to here sometime
mappairs(kmap, vmap, vec::AbstractVector;kw...) = map(vmap, vec)


"""
Map a function, which may depend on the key, across the values of a dictionary.
"""
function mapvals(f, pairs::T; keys::Bool=false, iter::Bool=false) where T<:AbstractDict
  (iter ? identity : dicttype(T))(if keys
    (k => f(k,v) for (k,v) in pairs)
  else
    (k => f(v) for (k,v) in pairs)
  end)
end
function mapvals(f, collection; keys::Bool=false, iter::Bool=false)
  do_map = iter ? Iterators.map : map
  if keys
    do_map(f, eachindex(collection), values(collection))
  else
    do_map(f, values(collection))
  end
end

dicttype(::Type{T}) where T <: AbstractDict = T.name.wrapper
dicttype(::Type{<:Iterators.Pairs}) = Dict

@inline make_map(f, xs) = make_map(f, xs, Any)

"""
Maps `f` over a `UnitRange` to produce a `Vector`,
or else over anything to produce a `Dict`. The type parameter
functions to ensure the return type is as desired even when the
input is empty.
"""
function make_map(f, xs::UnitRange{Int}, ::Type{T}) where T
  if isempty(xs)
    T[]
  else
    ys = map(f, xs)
    eltype(ys) <: T || error("Element(s) of $ys are not instances of $T")
    ys
  end
end

function make_map(f, xs, ::Type{T}) where T
  if isempty(xs)
    Dict{eltype(xs),T}()
  else
    xys = Dict(x => f(x) for x in xs)
    valtype(xys) <: T || error("Value(s) of $xys are not instances of $T")
    xys
  end
end

# Theory of FinDomFunctors
##########################

"""
Theory of functors with a finitely-presented domain (ob and hom generators). The
functor assigns codom homs to dom *generators*. This theory itself is ambivalent
to whether the codomain category is finitely presented.
"""
@theory ThFinDomFunctor <: ThFunctor begin
  DomGen::TYPE;
  gen_map(o::DomGen)::CodomHom
end

# Wrapper type for models of ThFinDomFunctor
############################################

""" A functor out of a finitely-presented category into a category.

Wrapper type for models of `ThFinDomFunctor`.
"""
ThFinDomFunctor.Meta.@typed_wrapper FinDomFunctor′ <: AbsFunctor


const FinFunctor{A,B,C,D,E} = FinDomFunctor′{A,B,C,D,FinCat,FinCat,E}
const FinDomFunctor{A,B,C,D,E} = FinDomFunctor′{A,B,C,D,FinCat,Cat,E}
const FunctorFinDom = Union{FinFunctor, FinDomFunctor}

FinDomFunctor(impl) = 
  FinDomFunctor{impl_type.(Ref(impl), Ref(ThFinDomFunctor), 
                [:DomOb,:CodomOb,:DomHom,:CodomHom,:DomGen])...}(impl)
"""
If we want this partially specified type to act as a constructor, we 
need to fill in the other type parameters.
"""
function FinFunctor(impl) 
  DO, CO, DH, CH, DG = impl_type.(Ref(impl), Ref(ThFinDomFunctor), 
                                  [:DomOb,:CodomOb,:DomHom,:CodomHom,:DomGen])

  FinFunctor{DO, CO, DH, CH, DG}(impl)
end 

function validate(i::FinDomFunctor′)
  DO, CO, DH, CH, DG = impl_type.(Ref(i),[:DomOb,:CodomOb,:DomHom, :CodomHom, :DomGen])
  𝒞, 𝒟 = ThFinDomFunctor.dom(i), ThFinDomFunctor.codom(i)
  𝒞O,𝒞H,𝒞G,𝒟O,𝒟H = impl_type.([𝒞,𝒞,𝒞,𝒟,𝒟],[:Ob,:Hom,:Gen,:Ob,:Hom])
  𝒞 isa FinCat || error("Bad dom FinCat $(typeof(𝒞))")
  𝒟 isa AbsCat || error("Bad codom Cat $𝒟")
  𝒞O == DO || error("Bad dom ob type $(𝒞O) ≠ $DO")
  𝒞H == DH || error("Bad dom hom type: $(𝒞H) ≠ $DH")
  𝒞G == DG || error("Bad dom gen type: $(𝒞G) ≠ $DG")
  CO == 𝒟O || error("Bad cod ob type: $(𝒟O) ≠ $CO")
  CH == 𝒟H || error("Bad cod hom type: $(𝒟H) ≠ $CH")
  i
end

# As a Functor
##############

""" Interpret a FinDomFunctor as a Functor

We need a new model struct for this because `dom` must return a `FinCat` in the
case of implementing `ThFinDomFunctor` but a `Category` in the case of
implementing `ThCategory`.
"""
@struct_hash_equal struct FinFunctorAsFunctor{DO, CO, DH, CH}
  val::FinDomFunctor′{DO, CO, DH, CH}
end 

GATlab.getvalue(f::FinFunctorAsFunctor) = f.val

@instance ThFunctor{DO,CO,DH,CH,Cat,Cat} [
    model::FinFunctorAsFunctor{DO, CO, DH, CH}] where {DO, CO, DH, CH} begin

  dom() = Category(dom(getvalue(model))) # coerce to Cat

  codom() = Category(codom(getvalue(model))) # coerce to Cat, if not already

  ob_map(x::DO)::CO = ob_map(model, x)

  hom_map(x::DH)::CH = hom_map(model, x)
end

# Other methods
###############

Base.show(io::IO, s::FinDomFunctor) = show(io, getvalue(s))

show_type_constructor(io::IO, ::Type{<:FinFunctor}) =
  print(io, "FinFunctor")

show_type_constructor(io::IO, ::Type{<:FinDomFunctor}) =
  print(io, "FinDomFunctor")

""" Collect assignments of functor's object map as a vector.
"""
collect_ob(F::FunctorFinDom) = map(x -> ob_map(F, x), ob_generators(dom(F)))

""" Collect assignments of functor's object map as a dictionary.
"""
ob_map(F::FunctorFinDom) = Dict(x=>ob_map(F, x) for x in  ob_generators(dom(F)))

""" Collect assignments of functor's morphism map as a vector.
"""
collect_hom(F::FunctorFinDom) = map(f -> gen_map(F, f), hom_generators(dom(F)))

""" Collect assignments of functor's morphism map as a dictionary.
"""
hom_map(F::FunctorFinDom) = 
  Dict(f => gen_map(F, f) for f in hom_generators(dom(F)))

""" Is the purported functor on a presented category functorial?

This function checks that functor preserves domains and codomains. When
`check_equations` is `true` (the default is `false`), it also purports to check
that the functor preserves all equations in the domain category. No nontrivial 
checks are currently implemented, so this only functions for identity functors.

See also: [`functoriality_failures'](@ref) and [`is_natural`](@ref).
"""
function is_functorial(F::FunctorFinDom; kw...)
  failures = functoriality_failures(F; kw...)
  all(isempty, failures)
end

""" Failures of the purported functor on a presented category to be functorial.

Similar to [`is_functorial`](@ref) (and with the same caveats) but returns
iterators of functoriality failures: one for domain incompatibilities, one for
codomain incompatibilities, and one for equations that are not satisfied.
"""
function functoriality_failures(F::FunctorFinDom; check_equations::Bool=false)
  C, D = dom(F), codom(F)
  bad_dom = Iterators.filter(hom_generators(C)) do f 
    dom(D, gen_map(F, f)) != ob_map(F, src(C,f))
  end 
  bad_cod = Iterators.filter(hom_generators(C)) do f 
    codom(D, gen_map(F, f)) != ob_map(F, tgt(C,f))
  end
  bad_eqs = if check_equations
    # TODO: Currently this won't check for nontrivial equalities
    Iterators.filter(equations(C)) do (lhs,rhs)
      gen_map(F,lhs) != gen_map(F,rhs)
    end
  else () end
  (bad_dom, bad_cod, bad_eqs)
end


""" Construct a `FinDomMap` from an existing `FinDomFunctor` """
function Base.map(F::Functor, f_ob, f_hom)
  C = dom(F)
  FinDomFunctor(map(x -> f_ob(ob_map(F, x)), ob_generators(C)),
                map(f -> f_hom(hom_map(F, f)), hom_generators(C)), C)
end


""" Force evaluation of lazily defined function or functor.
The resulting ob_map and hom_map are guaranteed to have 
valtype or eltype, as appropriate, equal to Ob and Hom,
respectively. 
"""
function force(F::FunctorFinDom, Obtype::Type=Any, Homtype::Type=Any)
  C = dom(F)
  FinDomFunctor(
    make_map(x -> ob_map(F, x), ob_generators(C), Obtype),
    make_map(f -> gen_map(F,f), hom_generators(C), Homtype), 
    C, codom(F); homtype=:hom)
end

""" Obtain a FreeDiagram from a FinDomFunctor """
function FreeDiagram(f::FunctorFinDom)
  obs = collect_ob(f)
  obdict = Dict(o => i for (i, o) in enumerate(obs))
  D = codom(f)
  homs = [(h, obdict[dom(D,h)], obdict[codom(D,h)]) for h in collect_hom(f)]

  FreeDiagram(FreeGraph{obtype(D), homtype(D)}(obs, homs))
end


dom_cat(F::FinDomFunctor)::Category = Category(dom(F))

function codom_cat(F::FinDomFunctor)::Category
  𝒞 = codom(F) 
  𝒞 isa Category && return 𝒞
  𝒞 isa FinCat && return Category(𝒞)
  error("Bad codom to $F: $𝒞 ")
end

""" Create a composite FinDomFunctorMap """
function compose_abs_functor(F::FunctorFinDom, G::AbsFunctor)
  C, D = dom(F), codom(G)
  FF = D isa FinCat ? FinFunctor : FinDomFunctor
  FF(mapvals(fx -> ob_map(G, fx), ob_map(F)),
                mapvals(fx -> hom_map(G, fx), hom_map(F)), C, D; 
                homtype=:hom)
end

""" Create a composite FunctorCallable """
function compose_abs_functor(F::AbsFunctor, G::AbsFunctor)
  Functor(x -> ob_map(G,  ob_map(F, x)),
          x -> hom_map(G, hom_map(F, x)), dom(F), codom(G))
end


# Initial functors
##################

"""
Dual to a [final functor](https://ncatlab.org/nlab/show/final+functor), an
*initial functor* is one for which pulling back diagrams along it does not
change the limits of these diagrams.

This amounts to checking, for a functor C->D, that, for every object d in
Ob(D), the comma category (F/d) is connected.
"""
function is_initial(F::FunctorFinDom)::Bool
  cod = codom(F)
  cod isa FinCat || error("Can only check initiality for functors with f.p. codom")
  Gₛ, Gₜ = Graph(dom(F)), Graph(cod)
  pathₛ, pathₜ = enumerate_paths.([Gₛ, Gₜ])

  function connected_nonempty_slice(t::Int)::Bool
    paths_into_t = incident(pathₜ, t, :tgt)
    # Generate slice objects
    ob_slice = Pair{Int,Vector{Int}}[] # s ∈ Ob(S) and a path ∈ T(F(s), t)
    for s in vertices(Gₛ)
      paths_s_to_t = incident(pathₜ, ob_map(F,s), :src) ∩ paths_into_t
      append!(ob_slice, [s => pathₜ[p, :eprops] for p in paths_s_to_t])
    end

    # Empty case
    isempty(ob_slice) && return false

    """
    For two slice objects (m,pₘ) and (n,pₙ) check for a morphism f ∈ S(M,N) such
    that there is a commutative triangle pₘ = f;pₙ
    """
    function check_pair(i::Int, j::Int)::Bool
      (m,pₘ), (n,pₙ) = ob_slice[i], ob_slice[j]
      es = incident(pathₛ, m, :src) ∩ incident(pathₛ, n, :tgt)
      paths = Path.(Ref(dom(F)), pathₛ[es, :eprops], m, n)
      return any(f -> pₘ == vcat(edges(hom_map(F,f))..., pₙ), paths)
    end

    # Use check_pair to determine pairwise connectivity
    connected = IntDisjointSets(length(ob_slice)) # sym/trans/refl closure
    obs = 1:length(ob_slice)
    for (i,j) in Base.Iterators.product(obs, obs)
      if !in_same_set(connected, i, j) && check_pair(i,j)
        union!(connected, i, j)
      end
    end
    return num_groups(connected) == 1
  end

  # Check for each t ∈ T whether F/t is connected
  return all(connected_nonempty_slice, 1:nv(Gₜ))
end
