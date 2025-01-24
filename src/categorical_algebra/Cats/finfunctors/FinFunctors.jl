export FinFunctor, FinDomFunctor, is_functorial, functoriality_failures, 
       collect_ob, collect_hom, force, is_initial, dom_to_graph, mapvals, make_map

using StructEquality
using DataStructures
using GATlab, ACSets
import GATlab: op
using ....Theories: ObExpr, HomExpr
using ....Graphs, ....BasicSets
using ..Cats 
import ....BasicSets: force
import ..Functors: ob_map, hom_map, component

# Functors
##########

""" A functor out of a finitely presented category.
"""
const FinDomFunctor{Dom<:FinCat,Codom<:Cat} = Functor{Dom,Codom}

FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCatGraph, codom::Cat) =
  FinDomFunctor(maps.V, maps.E, dom, codom)

function FinDomFunctor(ob_map, dom::FinCat, codom::Cat{Ob,Hom}) where {Ob,Hom}
  is_discrete(dom) ||
    error("Morphism map omitted by domain category is not discrete: $dom")
  FinDomFunctor(ob_map, empty(ob_map, Hom), dom, codom)
end
FinDomFunctor(ob_map, ::Nothing, dom::FinCat, codom::Cat) =
  FinDomFunctor(ob_map, dom, codom)

function hom_map(F::FinDomFunctor, path::Path)
  C, D = dom(F), codom(F)
  path = decompose(C, path)
  mapreduce(e -> hom_map(F, e), (gs...) -> compose(D, gs...),
             edges(path), init=id(D, ob_map(F, src(path))))
end
decompose(C::FinCatGraph, path::Path) = path
decompose(C::OppositeCat, path::Path) = reverse(path)

function hom_map(F::FinDomFunctor, f::GATExpr{:compose})
  C, D = dom(F), codom(F)
  mapreduce(f -> hom_map(F, f), (gs...) -> compose(D, gs...), decompose(C, f))
end
decompose(C::FinCatPresentation, f::GATExpr{:compose}) = args(f)
decompose(C::OppositeCat, f::GATExpr{:compose}) = reverse(decompose(C.cat, f))

function hom_map(F::FinDomFunctor, f::GATExpr{:id})
  id(codom(F), ob_map(F, dom(f)))
end

(F::FinDomFunctor)(expr::ObExpr) = ob_map(F, expr)
(F::FinDomFunctor)(expr::HomExpr) = hom_map(F, expr)

SetFunctions.show_type_constructor(io::IO, ::Type{<:FinDomFunctor}) =
  print(io, "FinDomFunctor")

""" Collect assignments of functor's object map as a vector.
"""
collect_ob(F::FinDomFunctor) = map(x -> ob_map(F, x), ob_generators(dom(F)))

""" Collect assignments of functor's morphism map as a vector.
"""
collect_hom(F::FinDomFunctor) = map(f -> hom_map(F, f), hom_generators(dom(F)))

""" Is the purported functor on a presented category functorial?

This function checks that functor preserves domains and codomains. When
`check_equations` is `true` (the default is `false`), it also purports to check
that the functor preserves all equations in the domain category. No nontrivial 
checks are currently implemented, so this only functions for identity functors.

See also: [`functoriality_failures'](@ref) and [`is_natural`](@ref).
"""
function is_functorial(F::FinDomFunctor; kw...)
  failures = functoriality_failures(F; kw...)
  all(isempty, failures)
end

""" Failures of the purported functor on a presented category to be functorial.

Similar to [`is_functorial`](@ref) (and with the same caveats) but returns
iterators of functoriality failures: one for domain incompatibilities, one for
codomain incompatibilities, and one for equations that are not satisfied.
"""
function functoriality_failures(F::FinDomFunctor; check_equations::Bool=false)
  C, D = dom(F), codom(F)
  bad_dom = Iterators.filter(hom_generators(C)) do f 
    dom(D, hom_map(F, f)) != ob_map(F, dom(C,f))
  end 
  bad_cod = Iterators.filter(hom_generators(C)) do f 
    codom(D, hom_map(F, f)) != ob_map(F, codom(C,f))
  end
  bad_eqs = if check_equations
    # TODO: Currently this won't check for nontrivial equalities
    Iterators.filter(equations(C)) do (lhs,rhs)
      !is_hom_equal(D,hom_map(F,lhs),hom_map(F,rhs))
    end
  else () end
  (bad_dom, bad_cod, bad_eqs)
end

function Base.map(F::Functor{<:FinCat,<:TypeCat}, f_ob, f_hom)
  C = dom(F)
  FinDomFunctor(map(x -> f_ob(ob_map(F, x)), ob_generators(C)),
                map(f -> f_hom(hom_map(F, f)), hom_generators(C)), C)
end

""" A functor between finitely presented categories.
"""
const FinFunctor{Dom<:FinCat,Codom<:FinCat} = FinDomFunctor{Dom,Codom}

FinFunctor(maps, dom::FinCat, codom::FinCat) = FinDomFunctor(maps, dom, codom)
FinFunctor(ob_map, hom_map, dom::FinCat, codom::FinCat) =
  FinDomFunctor(ob_map, hom_map, dom, codom)
FinFunctor(ob_map, hom_map, dom::Presentation, codom::Presentation) =
  FinDomFunctor(ob_map, hom_map, FinCat(dom), FinCat(codom))

SetFunctions.show_type_constructor(io::IO, ::Type{<:FinFunctor}) =
  print(io, "FinFunctor")

""" Force evaluation of lazily defined function or functor.
The resulting ob_map and hom_map are guaranteed to have 
valtype or eltype, as appropriate, equal to Ob and Hom,
respectively. 
"""
function force(F::FinDomFunctor, Obtype::Type=Any, Homtype::Type=Any)
  C = dom(F)
  FinDomFunctor(
    make_map(x -> ob_map(F, x), ob_generators(C), Obtype),
    make_map(f -> hom_map(F,f), hom_generators(C), Homtype), 
    C)
end


"""
Reinterpret a functor on a finitely presented category
as a functor on the equivalent category (ignoring equations)
free on a graph. Also normalizes the input to have vector ob_map
and hom_map, with valtype optionally specified. This is useful when
the domain is empty or when the maps might be tightly typed but need to
allow for types such as that of identity morphisms upon mutation.
"""
function dom_to_graph(F::FinDomFunctor{Dom,<:Cat{Ob,Hom}},obtype=Ob,homtype=Hom) where {Dom,Ob,Hom} 
  D = dom(F)
  C = FinCat(graph(D))
  new_obs = obtype[ob_map(F,ob) for ob in ob_generators(D)]
  new_homs = homtype[hom_map(F,hom) for hom in hom_generators(D)]
  FinDomFunctorMap(new_obs,new_homs,C,TypeCat(obtype,homtype))
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
function is_initial(F::FinFunctor)::Bool
  Gₛ, Gₜ = graph(dom(F)), graph(codom(F))
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
      paths = pathₛ[es, :eprops]
      return any(f -> pₘ == vcat(edges.(hom_map(F,f))..., pₙ), paths)
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
or else over anything to produce a `Dict`. The type paramter
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

hom_map(F::FinDomFunctor{<:DiscreteCat}, x) = id(codom(F), ob_map(F, x))
