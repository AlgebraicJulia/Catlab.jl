module FinFunctors 
export FinDomFunctor, is_functorial, functoriality_failures, is_initial, 
        collect_ob, collect_hom, make_map, components, gen_map, dom_to_graph

using DataStructures: IntDisjointSets, in_same_set, num_groups
using StructEquality
using Reexport
using GATlab, ACSets

import ....Theories: dom, codom
using ....Graphs
using ..Categories
using ..Functors: FunctorImpl, ThFunctor, Functor
import ..Functors: ob_map, hom_map, show_type_constructor
import ..FreeDiagrams: FreeDiagram
import ...BasicSets: force


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
Theory of functors with a finitely-presented domain (ob and hom generators).
The functor assigns codom homs to dom *generators*.
"""
@theory ThFinDomFunctor begin
  DomOb::TYPE; CodomOb::TYPE; DomHom::TYPE; CodomHom::TYPE; DomGen::TYPE; 
  FCat::TYPE; Cat′::TYPE;
  dom()::FCat
  codom()::Cat′
  ob_map(o::DomOb)::CodomOb
  gen_map(o::DomGen)::CodomHom
end

""" Subtypes of this must implement `ThFinDomFunctor` """
abstract type FinDomFunctorImpl{DO,CO,DH,CH,DG} <: Model{
  Tuple{DO,CO,DG,CH,FinCat,Cat}} end 

# Wrapper type for models of ThFinDomFunctor
############################################
""" A functor out of a finitely-presented category.

Wrapper type for models of `ThFinDomFunctor`.
"""
struct FinDomFunctor{DO,CO,DH,CH,DG} <: FunctorImpl{DO,CO,DH,CH}
  impl::FinDomFunctorImpl{DO,CO,DH,CH,DG}
  function FinDomFunctor(i::FinDomFunctorImpl{DO,CO,DH,CH,DG}) where {DO,CO,DH,CH,DG}
    # check types
    D, C = ThFinDomFunctor.dom[i](), ThFinDomFunctor.codom[i]()
    obtype(D) == DO || error("Bad dom ob type")
    homtype(D) == DH || error("Bad dom hom type")
    gentype(D) == DG || error("Bad dom hom type")
    obtype(C) == CO || error("Bad dom ob type")
    homtype(C) == CH || error("Bad dom hom type")
    new{DO,CO,DH,CH,DG}(i)
  end 
end

GATlab.getvalue(f::FinDomFunctor) = f.impl

# Access model methods
######################

dom(f::FinDomFunctor) = ThFinDomFunctor.dom[getvalue(f)]()

codom(f::FinDomFunctor) = ThFinDomFunctor.codom[getvalue(f)]()

ob_map(f::FinDomFunctor, x) = ThFinDomFunctor.ob_map[getvalue(f)](x)

gen_map(f::FinDomFunctor, x) = ThFinDomFunctor.gen_map[getvalue(f)](x)

# Other methods
###############

""" Apply a FinDomFunctor to a path of generators """
function path_map(F::FinDomFunctor, path::Path)
  C, D = dom(F), codom(F)
  init = id(D, ob_map(F, src(path)))
  mapreduce(e -> gen_map(F, e), (gs...) -> compose(D, gs...), edges(path); init)
end

""" Apply a FinDomFunctor defined on generators by decompose the hom into a path of generators """
function hom_map(F::FinDomFunctor, h)
  path_map(F, decompose(dom(F), h))
end

Base.show(io::IO, s::FinDomFunctor) = show(io, getvalue(s))

show_type_constructor(io::IO, ::Type{<:FinDomFunctor}) =
  print(io, "FinDomFunctor")

""" Collect assignments of functor's object map as a vector.
"""
collect_ob(F::FinDomFunctor) = map(x -> ob_map(F, x), ob_generators(dom(F)))

""" Collect assignments of functor's morphism map as a vector.
"""
collect_hom(F::FinDomFunctor) = map(f -> gen_map(F, f), hom_generators(dom(F)))

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
    dom(D, gen_map(F, f)) != ob_map(F, src(C,f))
  end 
  bad_cod = Iterators.filter(hom_generators(C)) do f 
    codom(D, gen_map(F, f)) != ob_map(F, tgt(C,f))
  end
  bad_eqs = if check_equations
    # TODO: Currently this won't check for nontrivial equalities
    Iterators.filter(equations(C)) do (lhs,rhs)
      !is_hom_equal(D,gen_map(F,lhs),gen_map(F,rhs))
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

# Implementations
#################
include("FunctorImpls/FinFunctorImpls/IdFinFunctor.jl")
include("FunctorImpls/FinFunctorImpls/OpFinFunctor.jl")
include("FunctorImpls/FinFunctorImpls/FinDomMap.jl")
include("FunctorImpls/FinFunctorImpls/ACSetFunctors.jl")
include("FunctorImpls/FinFunctorImpls/CompFinFunctor.jl")

@reexport using .IdFinFunctor
@reexport using .OpFinFunctor
@reexport using .FinDomMap
@reexport using .ACSetFunctors
@reexport using .CompFinFunctor



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
    C, codom(F))
end

function FreeDiagram(F::FinDomFunctor)
  C, D = dom(F), codom(F)
  diagram = FreeDiagram{obtype(D),homtype(D)}()
  ob_dict = Dict(map(ob_generators(C)) do x 
    x => add_vertex!(diagram; ob=ob_map(F, x))
  end)
  for h in hom_generators(C)
    add_edge!(diagram, ob_dict[dom(C,h)], ob_dict[codom(C,h)], hom=hom_map(F,h))
  end
  diagram 
end

# """ Wrapper type to interpret `FreeDiagram` as a `FinDomFunctor`.
# """
# @struct_hash_equal struct FreeDiagramFunctor{Ob,Hom,Codom} <:
#     FinDomFunctor{FreeCatGraph{AbstractFreeDiagram{<:Any,Tuple{Ob,Hom}}},Codom}
#   diagram::FreeDiagram{Ob,Hom}
#   codom::Codom
# end

# FinDomFunctor(diagram::FreeDiagram, codom::Cat) =
#   FreeDiagramFunctor(diagram, codom)

# FinDomFunctor(diagram::FreeDiagram{Ob,Hom}) where {Ob,Hom} =
#   FreeDiagramFunctor(diagram, TypeCat(Ob, Hom))

# dom(F::FreeDiagramFunctor) = FreeCatGraph(getvalue(F.diagram))

# Categories.do_ob_map(F::FreeDiagramFunctor, x) = ob(F.diagram, x)

# Categories.do_hom_map(F::FreeDiagramFunctor, f) = hom(F.diagram, f)

# collect_ob(F::FreeDiagramFunctor) = ob(F.diagram)

# collect_hom(F::FreeDiagramFunctor) = hom(F.diagram)


"""
Reinterpret a functor on a finitely presented category
as a functor on the equivalent category (ignoring equations)
free on a graph. Also normalizes the input to have vector ob_map
and hom_map, with valtype optionally specified. This is useful when
the domain is empty or when the maps might be tightly typed but need to
allow for types such as that of identity morphisms upon mutation.
"""
function dom_to_graph(F::FinDomFunctor)
  D = dom(F)
  C = FinCat(graph(D))
  new_obs = obtype[ob_map(F,ob) for ob in ob_generators(D)]
  new_homs = homtype[hom_map(F,hom) for hom in hom_generators(D)]
  FinDomFunctorMap(new_obs,new_homs,C,TypeCat(obtype,homtype))
end

function Base.show(io::IO, F::T) where T <: FinDomFunctorMap
  Categories.show_type_constructor(io, T); print(io, "(")
  show(io, F.ob_map)
  print(io, ", ")
  show(io, F.hom_map)
  print(io, ", ")
  Categories.show_domains(io, F)
  print(io, ")")
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
function is_initial(F::FinDomFunctor)::Bool
  cod = getvalue(codom(F))
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


end # module