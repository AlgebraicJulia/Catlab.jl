""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetTransformation, CSetTransformation,
  TightACSetTransformation, LooseACSetTransformation, SubACSet, SubCSet,
  ACSetHomomorphismAlgorithm, BacktrackingSearch, HomomorphismQuery,
  components, force, is_natural, homomorphism, homomorphisms, is_homomorphic,
  isomorphism, isomorphisms, is_isomorphic,
  generate_json_acset, parse_json_acset, read_json_acset, write_json_acset,
  uncurry, curry, ACSetCat

using Base.Iterators: flatten
using Base.Meta: quot
using AutoHashEquals
using JSON
using Reexport
using Tables
using DataStructures: DefaultDict

@reexport using ...CSetDataStructures
using ...GAT, ...Present
using ...Theories: Category, SchemaDescType, CSetSchemaDescType,
  attrtype, attrtype_num, attr, adom, acodom, acodom_nums
import ...Theories: dom, codom, compose, ⋅, id,
  ob, hom, meet, ∧, join, ∨, top, ⊤, bottom, ⊥, curry
using ..FreeDiagrams, ..Limits, ..Subobjects, ..FinSets, ..FinCats
import ..Limits: limit, colimit, universal, pushout_complement,
  can_pushout_complement
import ..Subobjects: Subobject, SubobjectBiHeytingAlgebra,
  implies, ⟹, subtract, \, negate, ¬, non, ~
import ..Categories: is_hom_equal
import ..Sets: SetOb, SetFunction, TypeSet
import ..FinSets: FinSet, FinFunction, FinDomFunction, force, predicate
import ..FinCats: FinDomFunctor, components, is_natural, FinTransformationMap,
                  FinDomFunctorMap

# Sets interop
##############

""" Create `SetOb` for object or attribute type of attributed C-set.

For objects, the result is a `FinSet`; for attribute types, a `TypeSet`.
"""
@inline SetOb(X::StructACSet, type::Symbol)::SetOb = set_ob(X, Val{type})

@generated function set_ob(X::StructACSet{S,Ts},
                           ::Type{Val{type}}) where {S,Ts,type}
  if type ∈ ob(S)
    :(FinSet(X, $(Meta.quot(type))))
  elseif type ∈ attrtype(S)
    T = Ts.parameters[attrtype_num(S, type)]
    :(TypeSet{$T}())
  else
    throw(ArgumentError("$(repr(type)) not in $(ob(S)) or $(attrtype(S))"))
  end
end

""" Create `FinSet` for object of attributed C-set.
"""
@inline FinSet(X::StructACSet, type::Symbol) = FinSets.FinSetInt(nparts(X, type))

""" Create `TypeSet` for object or attribute type of attributed C-set.
"""
@inline TypeSet(X::StructACSet, type::Symbol)::TypeSet = type_set(X, Val{type})

@generated function type_set(X::StructACSet{S,Ts},
                             ::Type{Val{type}}) where {S,Ts,type}
  T = if type ∈ ob(S)
    Int
  elseif type ∈ attrtype(S)
    Ts.parameters[attrtype_num(S, type)]
  else
    throw(ArgumentError("$(repr(type)) not in $(ob(S)) or $(attrtype(S))"))
  end
  :(TypeSet{$T}())
end

""" Create `SetFunction` for morphism or attribute of attributed C-set.

For morphisms, the result is a `FinFunction`; for attributes, a
`FinDomFunction`.
"""
@inline SetFunction(X::StructACSet, name::Symbol)::SetFunction =
  set_function(X, Val{name})

@generated function set_function(X::StructACSet{S,Ts,Idxed},
                                 ::Type{Val{name}}) where {S,Ts,Idxed,name}
  if name ∈ ob(S) || name ∈ attrtype(S)
    :(SetFunction(identity, SetOb(X, $(Meta.quot(name)))))
  elseif name ∈ hom(S)
    quote
      FinFunction(subpart(X, $(Meta.quot(name))),
                  FinSet(X, $(Meta.quot(codom(S, name)))),
                  index=$(Idxed[name] ? :(X.hom_indices.$name) : false))
    end
  elseif name ∈ attr(S)
    :(FinDomFunction(X, $(Meta.quot(name))))
  else
    throw(ArgumentError("$(repr(name)) does not belong to schema $S"))
  end
end

""" Create `FinFunction` for morphism of attributed C-set.

Indices are included whenever they exist.
"""
@inline FinFunction(X::StructACSet, name::Symbol)::FinFunction =
  set_function(X, Val{name})

""" Create `FinDomFunction` for morphism or attribute of attributed C-set.

Indices are included whenever they exist. Unlike the `FinFunction` constructor,
the codomain of the result is always of type `TypeSet`.
"""
@inline FinDomFunction(X::StructACSet, name::Symbol)::FinDomFunction =
  fin_dom_function(X, Val{name})

@generated function fin_dom_function(X::StructACSet{S,Ts,Idxed},
    ::Type{Val{name}}) where {S,Ts,Idxed,name}
  if name ∈ ob(S)
    quote
      n = nparts(X, $(Meta.quot(name)))
      FinDomFunction(1:n, FinSet(n), TypeSet{Int}())
    end
  elseif name ∈ hom(S) || name ∈ attr(S)
    index_name = name ∈ hom(S) ? :hom_indices : :attr_indices
    quote
      FinDomFunction(subpart(X, $(Meta.quot(name))),
                     index=$(Idxed[name] ? :(X.$index_name.$name) : false))
    end
  else
    throw(ArgumentError(
      "$(repr(name)) not in $(ob(S)), $(hom(S)), or $(attr(S))"))
  end
end

# Categories interop
####################

# ACSets as set-valued FinDomFunctors.

# TODO: We should wrap `SchemaDescType` instead of creating a presentation.
const ACSetDomCat = FinCats.FinCatPresentation{
  Symbol, Union{FreeSchema.Ob,FreeSchema.AttrType},
  Union{FreeSchema.Hom,FreeSchema.Attr,FreeSchema.AttrType}}
const FinSetCat = TypeCat{SetOb,FinDomFunction{Int}}

""" Wrapper type to interpret attributed C-set as a functor.
"""
@auto_hash_equals struct ACSetFunctor{ACS<:ACSet} <:
    Functor{ACSetDomCat,FinSetCat}
  acset::ACS
  eqs::Vector{Pair}
end
FinDomFunctor(X::ACSet; eqs=Pair[]) = ACSetFunctor(X, eqs)

function dom(F::ACSetFunctor)
  p = Presentation(F.acset)
  for (l,r) in F.eqs
    add_equation!(p, l, r)
  end
  FinCat(p)
end
codom(F::ACSetFunctor) = TypeCat{SetOb,FinDomFunction{Int}}()

Categories.do_ob_map(F::ACSetFunctor, x) = SetOb(F.acset, x)
Categories.do_hom_map(F::ACSetFunctor, f) = SetFunction(F.acset, f)

# Set-valued FinDomFunctors as ACSets.

function (::Type{ACS})(F::FinDomFunctor) where ACS <: ACSet
  X = if ACS isa UnionAll
    pres = presentation(dom(F))
    Base.invokelatest(
      ACS{(eltype(ob_map(F, c)) for c in generators(pres, :AttrType))...})
  else
    Base.invokelatest(ACS)
  end
  copy_parts!(X, F)
  return X
end

""" Copy parts from a set-valued `FinDomFunctor` to an `ACSet`.
"""
function ACSetInterface.copy_parts!(X::ACSet, F::FinDomFunctor)
  pres = presentation(dom(F))
  added = Dict(Iterators.map(generators(pres, :Ob)) do c
    c = nameof(c)
    c => add_parts!(X, c, length(ob_map(F, c)::FinSet{Int}))
  end)
  for f in generators(pres, :Hom)
    dom_parts, codom_parts = added[nameof(dom(f))], added[nameof(codom(f))]
    set_subpart!(X, dom_parts, nameof(f), codom_parts[collect(hom_map(F, f))])
  end
  for f in generators(pres, :Attr)
    dom_parts = added[nameof(dom(f))]
    set_subpart!(X, dom_parts, nameof(f), collect(hom_map(F, f)))
  end
  added
end

# C-set transformations
#######################

""" Transformation between attributed C-sets.

Homomorphisms of attributed C-sets generalize homomorphisms of C-sets
([`CSetTransformation`](@ref)), which the user should understand before reading
further.

A homomorphism of attributed C-sets with schema S: C ↛ A (a profunctor) is a
natural transformation between the corresponding functors col(S) → Set, where
col(S) is the collage of S. When the components on attribute types, indexed by
objects of A, are all identity functions, the morphism is called *tight*; in
general, it is called *loose*. The terms "tight" and "loose" come from what the
nLab calls an ["M-category"](https://ncatlab.org/nlab/show/M-category). The
category of acsets on a fixed schema S is an M-category. Calling
`ACSetTransformation` will construct a tight or loose morphism as appropriate,
depending on which components are specified.

Since every tight morphism can be considered a loose one, the distinction
between tight and loose may seem an unimportant technicality, but it can have
important consequences because choosing one or the other greatly affects limits
and colimits of acsets. In practice, the tight morphisms suffice for most
purposes, including computing colimits. However, when computing limits of
acsets, the loose morphism are usually preferable.
"""
abstract type ACSetTransformation{S<:SchemaDescType,Comp,
                                  Dom<:StructACSet{S},Codom<:StructACSet{S}} end
# FIXME: The components `Comp` shouldn't be a type parameter in this abstract
# type but for now it is retained for backwards compatibility.

ACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where S =
  ACSetTransformation{S}(components, X, Y)
ACSetTransformation(X::StructACSet{S}, Y::StructACSet{S}; components...) where S =
  ACSetTransformation{S}((; components...), X, Y)

function ACSetTransformation{S}(components, X::StructACSet{S}, Y::StructACSet{S}) where S
  ob_components = filter(∈(ob(S))∘first, pairs(components))
  type_components = filter(∈(attrtype(S))∘first, pairs(components))
  length(ob_components) + length(type_components) == length(components) ||
    error("Not all names in $(keys(components)) are objects or attribute types")
  if isempty(type_components)
    TightACSetTransformation{S}(ob_components, X, Y)
  else
    LooseACSetTransformation{S}(ob_components, type_components, X, Y)
  end
end

components(α::ACSetTransformation) = α.components
force(α::ACSetTransformation) = map_components(force, α)
is_hom_equal(f::ACSetTransformation, g::ACSetTransformation) =
  force(f) == force(g)

""" Transformation between C-sets.

Recall that a C-set homomorphism is a natural transformation: a transformation
between functors C → Set satisfying the naturality axiom for every (generating)
morphism in C.

This data type records the data of a C-set transformation. Naturality is not
strictly enforced but is expected to be satisfied. It can be checked using the
function [`is_natural`](@ref).
"""
const CSetTransformation{S<:CSetSchemaDescType,Comp,
  Dom<:StructCSet{S},Codom<:StructCSet{S}} = ACSetTransformation{S,Comp,Dom,Codom}

CSetTransformation(components, X::StructCSet, Y::StructCSet) =
  TightACSetTransformation(components, X, Y)
CSetTransformation(X::StructCSet, Y::StructCSet; components...) =
  TightACSetTransformation((; components...), X, Y)

""" Tight transformation between attributed C-sets.

See [`ACSetTranformation`](@ref) for the distinction between tight and loose.
"""
@auto_hash_equals struct TightACSetTransformation{
    S <: SchemaDescType, Comp <: NamedTuple,
    Dom <: StructACSet{S}, Codom <: StructACSet{S}} <: ACSetTransformation{S,Comp,Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom

  function TightACSetTransformation{S}(components, X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    @assert keys(components) ⊆ ob(S)
    components = NamedTuple(
      c => coerce_component(c, get(components,c,1:0), nparts(X,c), nparts(Y,c))
      for c in ob(S))
    new{S,typeof(components),Dom,Codom}(components, X, Y)
  end
end
TightACSetTransformation(components, X::StructACSet{S}, Y::StructACSet{S}) where S =
  TightACSetTransformation{S}(components, X, Y)

function coerce_component(ob::Symbol, f::FinFunction{Int,Int},
                          dom_size::Int, codom_size::Int)
  length(dom(f)) == dom_size || error("Domain error in component $ob")
  length(codom(f)) == codom_size || error("Codomain error in component $ob")
  return f
end
coerce_component(ob::Symbol, f, dom_size::Int, codom_size::Int) =
  FinFunction(f, dom_size, codom_size)

function Base.getindex(α::TightACSetTransformation{S}, c) where S
  get(α.components, c) do
    c ∈ attrtype(S) || error("No object or attribute type with name $c")
    SetFunction(identity, TypeSet(dom(α),c), TypeSet(codom(α),c))
  end
end

type_components(α::TightACSetTransformation{S}) where S =
  NamedTuple(c => SetFunction(identity, TypeSet(dom(α),c), TypeSet(codom(α),c))
             for (i, c) in enumerate(attrtype(S)))

map_components(f, α::TightACSetTransformation) =
  TightACSetTransformation(map(f, components(α)), dom(α), codom(α))

function Base.show(io::IO, α::TightACSetTransformation)
  print(io, "ACSetTransformation(")
  show(io, components(α))
  print(io, ", ")
  Categories.show_domains(io, α)
  print(io, ")")
end

""" Loose transformation between attributed C-sets.

See [`ACSetTranformation`](@ref) for the distinction between tight and loose.
"""
@auto_hash_equals struct LooseACSetTransformation{
    S <: SchemaDescType, Comp <: NamedTuple, TypeComp <: NamedTuple,
    Dom <: StructACSet{S}, Codom <: StructACSet{S}} <: ACSetTransformation{S,Comp,Dom,Codom}
  components::Comp
  type_components::TypeComp
  dom::Dom
  codom::Codom

  function LooseACSetTransformation{S}(components, type_components,
                                       X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    @assert keys(components) ⊆ ob(S) && keys(type_components) ⊆ attrtype(S)
    components = NamedTuple(
      c => coerce_component(c, get(components,c,1:0), nparts(X,c), nparts(Y,c))
      for c in ob(S))
    type_components = NamedTuple(
      type => coerce_type_component(type, get(type_components, type, identity),
                                    Dom.parameters[i], Codom.parameters[i])
      for (type, i) in zip(attrtype(S), acodom_nums(S)))
    new{S,typeof(components),typeof(type_components),Dom,Codom}(
      components, type_components, X, Y)
  end
end
LooseACSetTransformation(components, type_components,
                         X::StructACSet{S}, Y::StructACSet{S}) where S =
  LooseACSetTransformation{S}(components, type_components, X, Y)

function coerce_type_component(type::Symbol, f::SetFunction,
                               dom_type::Type, codom_type::Type)
  dom_type <: eltype(dom(f)) || error("Domain error in component $type")
  eltype(codom(f)) <: codom_type || error("Codomain error in component $type")
  return f
end
function coerce_type_component(type::Symbol, ::Nothing,
                               dom_type::Type, codom_type::Type)
  codom_type == Nothing || error("Codomain error in component $type")
  ConstantFunction(nothing, TypeSet(dom_type))
end
coerce_type_component(type::Symbol, f, dom_type::Type, codom_type::Type) =
  SetFunction(f, TypeSet(dom_type), TypeSet(codom_type))

type_components(α::LooseACSetTransformation) = α.type_components

function Base.getindex(α::LooseACSetTransformation, c::Symbol)
  get(α.components, c) do
    get(α.type_components, c) do
      error("No object or attribute type with name $c")
    end
  end
end

function Base.show(io::IO, α::LooseACSetTransformation)
  print(io, "ACSetTransformation(")
  show(io, merge(components(α), type_components(α)))
  print(io, ", ")
  Categories.show_domains(io, α)
  print(io, ")")
end

map_components(f, α::LooseACSetTransformation) =
  LooseACSetTransformation(map(f, components(α)), α.type_components, dom(α), codom(α))

function is_natural(α::ACSetTransformation{S}) where {S}
  X, Y = dom(α), codom(α)
  for (f, c, d) in flatten((zip(hom(S), dom(S), codom(S)),
                            zip(attr(S), adom(S), acodom(S))))
    Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
    all(i -> Yf[α_c(i)] == α_d(Xf[i]), eachindex(Xf)) || return false
  end
  return true
end

function (C::Type{ACS})(F::FinTransformationMap) where ACS <: ACSet
  Cd, CCd = C(dom(F)), C(codom(F))
  return CSetTransformation(Cd, CCd; components(F)...)
end


FinTransformationMap(f::ACSetTransformation; eqs=Pair[]) =
  FinTransformationMap(components(f),
                    FinDomFunctor(dom(f); eqs=eqs),
                    FinDomFunctor(codom(f); eqs=eqs))

# Category of C-sets
####################

@instance Category{StructACSet, ACSetTransformation} begin
  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::StructACSet) = TightACSetTransformation(map(id, sets(X)), X, X)

  function compose(α::ACSetTransformation, β::ACSetTransformation)
    # Question: Should we incur cost of checking that codom(β) == dom(α)?
    LooseACSetTransformation(
      map(compose, components(α), components(β)),
      map(compose, type_components(α), type_components(β)),
      dom(α), codom(β))
  end
end

function compose(α::TightACSetTransformation, β::TightACSetTransformation)
  TightACSetTransformation(map(compose, components(α), components(β)),
                           dom(α), codom(β))
end

@cartesian_monoidal_instance ACSet ACSetTransformation
@cocartesian_monoidal_instance ACSet ACSetTransformation

# Finding C-set transformations
###############################

""" Algorithm for finding homomorphisms between attributed ``C``-sets.
"""
abstract type ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using backtracking search.

This procedure uses the classic backtracking search algorithm for a
combinatorial constraint satisfaction problem (CSP). As is well known, the
homomorphism problem for relational databases is reducible to CSP. Since the
C-set homomorphism problem is "the same" as the database homomorphism problem
(insofar as attributed C-sets are "the same" as relational databases), it is
also reducible to CSP. Backtracking search for CSP is described in many computer
science textbooks, such as (Russell & Norvig 2010, *Artificial Intelligence*,
Third Ed., Chapter 6: Constraint satisfaction problems, esp. Algorithm 6.5). In
our implementation, the search tree is ordered using the popular heuristic of
"minimum remaining values" (MRV), also known as "most constrained variable.
"""
struct BacktrackingSearch <: ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using a conjunctive query.

This algorithm evaluates a conjunctive query (limit in `FinSet`) to find all
homomorphisms between two ``C``-sets. In fact, conjunctive queries are exactly
the *representable* functors from ``C``-sets to sets, so every conjunctive query
arises in this way, with the caveat that conjunctive queries may correspond to
to infinite ``C``-sets when ``C`` is infinite (but possibly finitely presented).
"""
struct HomomorphismQuery <: ACSetHomomorphismAlgorithm end

""" Find a homomorphism between two attributed ``C``-sets.

Returns `nothing` if no homomorphism exists. For many categories ``C``, the
``C``-set homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.

To restrict to *monomorphisms*, or homomorphisms whose components are all
injective functions, set the keyword argument `monic=true`. To restrict only
certain components to be injective or bijective, use `monic=[...]` or
`iso=[...]`. For example, setting `monic=[:V]` for a graph homomorphism ensures
that the vertex map is injective but imposes no constraints on the edge map.

To restrict the homomorphism to a given partial assignment, set the keyword
argument `initial`. For example, to fix the first source vertex to the third
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`.

Use the keyword argument `alg` to set the homomorphism-finding algorithm. By
default, a backtracking search algorithm is used ([`BacktrackingSearch`](@ref)).

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
  result = nothing
  backtracking_search(X, Y; kw...) do α
    result = α; return true
  end
  result
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
homomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphisms(X, Y, alg; kw...)

function homomorphisms(X::StructACSet{S}, Y::StructACSet{S},
                       alg::BacktrackingSearch; kw...) where {S}
  results = ACSetTransformation{S}[]
  backtracking_search(X, Y; kw...) do α
    push!(results, map_components(deepcopy, α)); return false
  end
  results
end

""" Is the first attributed ``C``-set homomorphic to the second?

This function generally reduces to [`homomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_homomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_homomorphic(X, Y, alg; kw...)

is_homomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(homomorphism(X, Y, alg; kw...))

""" Find an isomorphism between two attributed ``C``-sets, if one exists.

See [`homomorphism`](@ref) for more information about the algorithms involved.
"""
isomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphism(X, Y, alg; kw...)

isomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphism(X, Y, alg; iso=true, initial=initial)

""" Find all isomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`isomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
isomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphisms(X, Y, alg; kw...)

isomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphisms(X, Y, alg; iso=true, initial=initial)

""" Are the two attributed ``C``-sets isomorphic?

This function generally reduces to [`isomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_isomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_isomorphic(X, Y, alg; kw...)

is_isomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(isomorphism(X, Y, alg; kw...))

# Backtracking search
#--------------------

""" Internal state for backtracking search for ACSet homomorphisms.
"""
struct BacktrackingState{S <: SchemaDescType,
    Assign <: NamedTuple, PartialAssign <: NamedTuple, LooseFun <: NamedTuple,
    Dom <: StructACSet{S}, Codom <: StructACSet{S}}
  """ The current assignment, a partially-defined homomorphism of ACSets. """
  assignment::Assign
  """ Depth in search tree at which assignments were made. """
  assignment_depth::Assign
  """ Inverse assignment for monic components or if finding a monomorphism. """
  inv_assignment::PartialAssign
  """ Domain ACSet: the "variables" in the CSP. """
  dom::Dom
  """ Codomain ACSet: the "values" in the CSP. """
  codom::Codom
  type_components::LooseFun
end

function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
                             monic=false, iso=false, type_components=(;), initial=(;),
                             ) where {Ob, Hom, Attr, S<:SchemaDescType{Ob,Hom,Attr}}
  # Fail early if no monic/isos exist on cardinality grounds.
  if iso isa Bool
    iso = iso ? Ob : ()
  end
  for c in iso
    nparts(X,c) == nparts(Y,c) || return false
  end
  if monic isa Bool
    monic = monic ? Ob : ()
  end
  # Injections between finite sets are bijections, so reduce to that case.
  monic = unique([iso..., monic...])
  for c in monic
    nparts(X,c) <= nparts(Y,c) || return false
  end

  # Initialize state variables for search.
  assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
  assignment_depth = map(copy, assignment)
  inv_assignment = NamedTuple{Ob}(
    (c in monic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
  loosefuns = NamedTuple{Attr}(
    isnothing(type_components) ? identity : get(type_components, c, identity) for c in Attr)
  state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y,
                            loosefuns)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments)
      assign_elem!(state, 0, Val{c}, x, y) || return false
    end
  end

  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1)
end

function backtracking_search(f, state::BacktrackingState{S}, depth::Int) where {S}
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    if any(!=(identity), state.type_components)
      return f(LooseACSetTransformation{S}(
        state.assignment, state.type_components, state.dom, state.codom))
    else
      return f(ACSetTransformation(state.assignment, state.dom, state.codom))
    end
  elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return false
  end
  c, x = mrv_elem

  # Attempt all assignments of the chosen element.
  Y = state.codom
  for y in parts(Y, c)
    assign_elem!(state, depth, Val{c}, x, y) &&
      backtracking_search(f, state, depth + 1) &&
      return true
    unassign_elem!(state, depth, Val{c}, x)
  end
  return false
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState{S}, depth) where S
  mrv, mrv_elem = Inf, nothing
  Y = state.codom
  for c in ob(S), (x, y) in enumerate(state.assignment[c])
    y == 0 || continue
    n = count(can_assign_elem(state, depth, Val{c}, x, y) for y in parts(Y, c))
    if n < mrv
      mrv, mrv_elem = n, (c, x)
    end
  end
  (mrv, mrv_elem)
end

""" Check whether element (c,x) can be assigned to (c,y) in current assignment.
"""
function can_assign_elem(state::BacktrackingState, depth,
                         ::Type{Val{c}}, x, y) where c
  # Although this method is nonmutating overall, we must temporarily mutate the
  # backtracking state, for several reasons. First, an assignment can be a
  # consistent at each individual subpart but not consistent for all subparts
  # simultaneously (consider trying to assign a self-loop to an edge with
  # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
  # must keep track of which elements we have visited to avoid looping forever.
  ok = assign_elem!(state, depth, Val{c}, x, y)
  unassign_elem!(state, depth, Val{c}, x)
  return ok
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.

Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""
@generated function assign_elem!(state::BacktrackingState{S}, depth,
                                 ::Type{Val{c}}, x, y) where {S, c}
  quote
    y′ = state.assignment.$c[x]
    y′ == y && return true  # If x is already assigned to y, return immediately.
    y′ == 0 || return false # Otherwise, x must be unassigned.
    if !isnothing(state.inv_assignment.$c) && state.inv_assignment.$c[y] != 0
      # Also, y must unassigned in the inverse assignment.
      return false
    end

    # Check attributes first to fail as quickly as possible.
    X, Y = state.dom, state.codom
    $(map(zip(attr(S), adom(S), acodom(S))) do (f, c_, d)
         :($(quot(c_))!=c
             || state.type_components[$(quot(d))](subpart(X,x,$(quot(f))))
                 == subpart(Y,y,$(quot(f))) || return false)
      end...)

    # Make the assignment and recursively assign subparts.
    state.assignment.$c[x] = y
    state.assignment_depth.$c[x] = depth
    if !isnothing(state.inv_assignment.$c)
      state.inv_assignment.$c[y] = x
    end
    $(map(out_hom(S, c)) do (f, d)
        :(assign_elem!(state, depth, Val{$(quot(d))}, subpart(X,x,$(quot(f))),
                       subpart(Y,y,$(quot(f)))) || return false)
      end...)
    return true
  end
end

""" Unassign the element (c,x) in the current assignment.
"""
@generated function unassign_elem!(state::BacktrackingState{S}, depth,
                                   ::Type{Val{c}}, x) where {S, c}
  quote
    state.assignment.$c[x] == 0 && return
    assign_depth = state.assignment_depth.$c[x]
    @assert assign_depth <= depth
    if assign_depth == depth
      X = state.dom
      if !isnothing(state.inv_assignment.$c)
        y = state.assignment.$c[x]
        state.inv_assignment.$c[y] = 0
      end
      state.assignment.$c[x] = 0
      state.assignment_depth.$c[x] = 0
      $(map(out_hom(S, c)) do (f, d)
          :(unassign_elem!(state, depth, Val{$(quot(d))},
                           subpart(X,x,$(quot(f)))))
        end...)
    end
  end
end

""" Get assignment pairs from partially specified component of C-set morphism.
"""
partial_assignments(x::AbstractDict) = pairs(x)
partial_assignments(x::AbstractVector) =
  ((i,y) for (i,y) in enumerate(x) if !isnothing(y) && y > 0)

# FIXME: Should these accessors go elsewhere?
in_hom(S, c) = [dom(S,f) => f for f in hom(S) if codom(S,f) == c]
out_hom(S, c) = [f => codom(S,f) for f in hom(S) if dom(S,f) == c]

# Limits and colimits
#####################

""" Limit of attributed C-sets that stores the pointwise limits in Set.
"""
struct ACSetLimit{Ob <: StructACSet, Diagram, Cone <: Multispan{Ob},
                 Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

""" Colimit of attributed C-sets that stores the pointwise colimits in Set.
"""
struct ACSetColimit{Ob <: StructACSet, Diagram, Cocone <: Multicospan{Ob},
                    Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

# By default, products of acsets are taken w.r.t. loose acset morphisms, whereas
# coproducts of acsets are taken w.r.t. tight acset morphisms. We do not need to
# provide defaults for limits and colimits of non-discrete diagrams, because the
# type of the diagram's morphisms disambiguates the situation.

Limits.terminal(::Type{T}; kw...) where T <: ACSet =
  limit(EmptyDiagram{T}(LooseACSetTransformation); kw...)
Limits.product(X::ACSet, Y::ACSet; kw...) =
  limit(ObjectPair(X, Y, LooseACSetTransformation); kw...)
Limits.product(Xs::AbstractVector{<:ACSet}; kw...) =
  limit(DiscreteDiagram(Xs, LooseACSetTransformation); kw...)

Limits.initial(::Type{T}; kw...) where T <: ACSet =
  colimit(EmptyDiagram{T}(TightACSetTransformation); kw...)
Limits.coproduct(X::ACSet, Y::ACSet; kw...) =
  colimit(ObjectPair(X, Y, TightACSetTransformation); kw...)
Limits.coproduct(Xs::AbstractVector{<:ACSet}; kw...) =
  colimit(DiscreteDiagram(Xs, TightACSetTransformation); kw...)

# Compute limits and colimits in C-Set by reducing to those in Set using the
# "pointwise" formula for (co)limits in functor categories.

function limit(::Type{Tuple{ACS,Hom}}, diagram) where
    {S, ACS <: StructCSet{S}, Hom <: TightACSetTransformation}
  limits = map(limit, unpack_diagram(diagram))
  Xs = cone_objects(diagram)
  Y = Base.invokelatest(ACS)
  limit!(Y, diagram, Xs, limits)
end

function limit(::Type{Tuple{ACS,Hom}}, diagram) where
    {S, ACS <: StructACSet{S}, Hom <: LooseACSetTransformation}
  limits = map(limit, unpack_diagram(diagram, all=true))
  Xs = cone_objects(diagram)
  Y = if isempty(attrtype(S)); ACS() else
    ACSUnionAll = Base.typename(ACS).wrapper
    ACSUnionAll{(eltype(ob(limits[d])) for d in attrtype(S))...}()
  end

  result = limit!(Y, diagram, Xs, limits)
  for (f, c, d) in zip(attr(S), adom(S), acodom(S))
    Yfs = map((π, X) -> π ⋅ FinDomFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  result
end

function limit!(Y::StructACSet{S}, diagram, Xs, limits) where S
  for c in ob(S)
    add_parts!(Y, c, length(ob(limits[c])))
  end
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Yfs = map((π, X) -> π ⋅ FinFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  πs = pack_components(map(legs, limits), map(X -> Y, Xs), Xs)
  ACSetLimit(diagram, Multispan(Y, πs), limits)
end

function universal(lim::ACSetLimit, cone::Multispan)
  components = map(universal, lim.limits, unpack_diagram(cone))
  CSetTransformation(components, apex(cone), ob(lim))
end

function colimit(::Type{Tuple{ACS,Hom}}, diagram) where
    {S, Ts, ACS <: StructACSet{S,Ts}, Hom <: TightACSetTransformation}
  # Colimit of C-set without attributes.
  colimits = map(colimit, unpack_diagram(diagram))
  Xs = cocone_objects(diagram)
  Y = Base.invokelatest(ACS)
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Yfs = map((ι, X) -> FinFunction(X, f) ⋅ ι, legs(colimits[d]), Xs)
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs))

  # Set data attributes by canonical inclusion from attributes in diagram.
  for (attr, c, d) in zip(attr(S), adom(S), acodom_nums(S))
    T = Ts.parameters[d]
    data = Vector{Union{Some{T},Nothing}}(nothing, nparts(Y, c))
    for (ι, X) in zip(ιs, Xs)
      for i in parts(X, c)
        j = ι[c](i)
        if isnothing(data[j])
          data[j] = Some(subpart(X, i, attr))
        else
          val1, val2 = subpart(X, i, attr), something(data[j])
          val1 == val2 || error(
            "ACSet colimit does not exist: $attr attributes $val1 != $val2")
        end
      end
    end
    set_subpart!(Y, attr, map(something, data))
  end

  ACSetColimit(diagram, Multicospan(Y, ιs), colimits)
end

function universal(colim::ACSetColimit, cocone::Multicospan)
  components = map(universal, colim.colimits, unpack_diagram(cocone))
  ACSetTransformation(components, ob(colim), apex(cocone))
end

""" Diagram in C-Set → named tuple of diagrams in Set.
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet}; kw...) =
  map(DiscreteDiagram, unpack_sets(ob(discrete); kw...))
unpack_diagram(span::Multispan{<:ACSet}; kw...) =
  map(Multispan, sets(apex(span); kw...),
      unpack_components(legs(span); kw...))
unpack_diagram(cospan::Multicospan{<:ACSet}; kw...) =
  map(Multicospan, sets(apex(cospan); kw...),
      unpack_components(legs(cospan); kw...))
unpack_diagram(para::ParallelMorphisms{<:ACSet}; kw...) =
  map(ParallelMorphisms, unpack_components(hom(para); kw...))
unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
  map(ComposableMorphisms, unpack_components(hom(comp); kw...))

function unpack_diagram(diag::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}};
                        all::Bool=false) where {S, ACS <: StructACSet{S}}
  names = all ? flatten((ob(S), attrtype(S))) : ob(S)
  NamedTuple(c => map(diag, Ob=X->SetOb(X,c), Hom=α->α[c]) for c in names)
end

""" Vector of C-sets → named tuple of vectors of sets.
"""
function unpack_sets(Xs::AbstractVector{<:StructACSet{S}};
                     all::Bool=false) where S
  # XXX: The explicit use of `FinSet` and `TypeSet` is needed here for the
  # nullary case (empty vector) because the Julia compiler cannot infer the
  # return type of the more general `SetOb`.
  fin_sets = (c => map(X->FinSet(X,c), Xs) for c in ob(S))
  NamedTuple(all ?
    flatten((fin_sets, (d => map(X->TypeSet(X,d), Xs) for d in attrtype(S)))) :
    fin_sets)
end

""" Vector of C-set transformations → named tuple of vectors of functions.
"""
function unpack_components(αs::AbstractVector{<:ACSetTransformation{S}};
                           all::Bool=false) where S
  names = all ? flatten((ob(S), attrtype(S))) : ob(S)
  NamedTuple(c => map(α -> α[c], αs) for c in names)
end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(fs::NamedTuple{names}, doms, codoms) where names
  # XXX: Is there a better way?
  components = map((x...) -> NamedTuple{names}(x), fs...)
  map(ACSetTransformation, components, doms, codoms)
end

""" C-set → named tuple of sets.
"""
function sets(X::StructACSet{S}; all::Bool=false) where S
  names = all ? flatten((ob(S), attrtype(S))) : ob(S)
  NamedTuple(c => SetOb(X,c) for c in names)
end

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).
"""
function pushout_complement(pair::ComposablePair{<:ACSet})
  # Compute pushout complements pointwise in FinSet.
  components = map(pushout_complement, unpack_diagram(pair))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  g = hom(Subobject(codom(pair), g_components))
  k = ACSetTransformation(k_components, dom(pair), dom(g))
  return ComposablePair(k, g)
end

function can_pushout_complement(pair::ComposablePair{<:ACSet})
  all(can_pushout_complement, unpack_diagram(pair)) &&
    isempty(dangling_condition(pair))
end

"""
Check the dangling condition for a pushout comlement: m doesn't map a deleted
element d to an element m(d) ∈ G if m(d) is connected to something outside the
image of m.

For example, in the C-Set of graphs,

   e1
v1 --> v2

if e1 is not matched but either v1 or v2 are deleted, then e1 is dangling.
"""
function dangling_condition(pair::ComposablePair{<:StructACSet{S}}) where S
  l, m = pair
  orphans = map(components(l), components(m)) do l_comp, m_comp
    image = Set(collect(l_comp))
    Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
  end
  # check that for all morphisms in C, we do not map to an orphan
  results = Tuple{Symbol,Int,Int}[]
  for (morph, src_obj, tgt_obj) in zip(hom(S), dom(S), codom(S))
    n_src = parts(codom(m), src_obj)
    unmatched_vals = setdiff(n_src, collect(m[src_obj]))
    unmatched_tgt = map(x -> codom(m)[x,morph], collect(unmatched_vals))
    for unmatched_val in setdiff(n_src, collect(m[src_obj]))  # G/m(L) src
      unmatched_tgt = codom(m)[unmatched_val,morph]
      if unmatched_tgt in orphans[tgt_obj]
        push!(results, (morph, unmatched_val, unmatched_tgt))
      end
    end
  end
  results
end

# Sub-C-sets
############

""" Sub-C-set of a C-set.
"""
const SubCSet{S} = Subobject{<:StructCSet{S}}
const SubACSet{S} = Subobject{<:StructACSet{S}}

components(A::SubACSet) = map(Subobject, components(hom(A)))
force(A::SubACSet) = Subobject(force(hom(A)))

""" Sub-C-set represented componentwise as a collection of subsets.
"""
@auto_hash_equals struct SubACSetComponentwise{
    Ob<:ACSet, Comp<:NamedTuple} <: Subobject{Ob}
  ob::Ob
  components::Comp

  function SubACSetComponentwise(X::Ob, components::NamedTuple) where Ob<:ACSet
    X_sets = sets(X)
    @assert keys(components) ⊆ keys(X_sets)
    coerced_components = NamedTuple{keys(X_sets)}(
      coerce_subob_component(set, get(components, ob, 1:0))
      for (ob, set) in pairs(X_sets))
    new{Ob,typeof(coerced_components)}(X, coerced_components)
  end
end

Subobject(X::ACSet, components::NamedTuple) =
  SubACSetComponentwise(X, components)
Subobject(X::ACSet; components...) = Subobject(X, (; components...))

function coerce_subob_component(X::FinSet, subset::SubFinSet)
  X == ob(subset) ? subset :
    error("Set $X in C-set does not match set of subset $subset")
end
function coerce_subob_component(X::FinSet, f::FinFunction)
  X == codom(f) ? Subobject(f) :
    error("Set $X in C-set does not match codomain of inclusion $f")
end
coerce_subob_component(X::FinSet, f) = Subobject(X, f)

ob(A::SubACSetComponentwise) = A.ob
components(A::SubACSetComponentwise) = A.components

function hom(A::SubACSetComponentwise{T}) where T <: ACSet
  U, X = T(), ob(A)
  hom_components = map(collect∘hom, components(A))
  copy_parts!(U, X, hom_components)
  ACSetTransformation(hom_components, U, X)
end

@instance SubobjectBiHeytingAlgebra{ACSet,SubACSet} begin
  @import ob
  meet(A::SubACSet, B::SubACSet) = meet(A, B, SubOpBoolean())
  join(A::SubACSet, B::SubACSet) = join(A, B, SubOpBoolean())
  top(X::ACSet) = top(X, SubOpWithLimits())
  bottom(X::ACSet) = bottom(X, SubOpWithLimits())

  implies(A::SubACSet, B::SubACSet) = implies(A, B, SubOpBoolean())
  subtract(A::SubACSet, B::SubACSet) = subtract(A, B, SubOpBoolean())
  negate(A::SubACSet) = implies(A, bottom(ob(A)), SubOpBoolean())
  non(A::SubACSet) = subtract(top(ob(A)), A, SubOpBoolean())
end

function meet(A::SubACSet, B::SubACSet, ::SubOpBoolean)
  Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
    meet(A₀, B₀, SubOpBoolean())
  end)
end
function join(A::SubACSet, B::SubACSet, ::SubOpBoolean)
  Subobject(common_ob(A, B), map(components(A), components(B)) do A₀, B₀
    join(A₀, B₀, SubOpBoolean())
  end)
end
top(X::ACSet, ::SubOpBoolean) =
  Subobject(X, map(X₀ -> top(X₀, SubOpBoolean()), sets(X)))
bottom(X::ACSet, ::SubOpBoolean) =
  Subobject(X, map(X₀ -> bottom(X₀, SubOpBoolean()), sets(X)))

""" Implication of sub-C-sets.

By (Reyes et al 2004, Proposition 9.1.5), the implication ``A ⟹ B`` for two
sub-``C``-sets ``A,B ↪ X`` is given by

``x ∈ (A ⟹ B)(c) iff ∀f: c → c′, x⋅f ∈ A(c′) ⟹ x⋅f ∈ B(c′)``

for all ``c ∈ C`` and ``x ∈ X(c)``. By the definition of implication and De
Morgan's law in classical logic, this is equivalent to

``x ∉ (A ⟹ B)(c) iff ∃f: c → c′, x⋅f ∈ A(c′) ∧ x⋅f ∉ B(c′)``.

In this form, we can clearly see the duality to formula and algorithm for
subtraction of sub-C-sets ([`subtract`](@ref)).
"""
function implies(A::SubACSet{S}, B::SubACSet{S}, ::SubOpBoolean) where S
  X = common_ob(A, B)
  A, B = map(predicate, components(A)), map(predicate, components(B))
  D = map(X₀ -> trues(length(X₀)), sets(X))

  function unset!(c, x)
    D[c][x] = false
    for (c′,x′) in all_incident(X, Val{c}, x)
      if D[c′][x′]; unset!(c′,x′) end
    end
  end

  for c in ob(S), x in parts(X,c)
    if D[c][x] && A[c][x] && !B[c][x]; unset!(c,x) end
  end
  Subobject(X, D)
end

""" Subtraction of sub-C-sets.

By (Reyes et al 2004, Sec 9.1, pp. 144), the subtraction ``A ∖ B`` for two
sub-``C``-sets ``A,B ↪ X`` is given by

``x ∈ (A ∖ B)(c) iff ∃f: c′ → c, ∃x′ ∈ f⁻¹⋅x, x′ ∈ A(c′) ∧ x′ ∉ B(c′)``

for all ``c ∈ C`` and ``x ∈ X(c)``. Compare with [`implies`](@ref).
"""
function subtract(A::SubACSet{S}, B::SubACSet{S}, ::SubOpBoolean) where S
  X = common_ob(A, B)
  A, B = map(predicate, components(A)), map(predicate, components(B))
  D = map(X₀ -> falses(length(X₀)), sets(X))

  function set!(c, x)
    D[c][x] = true
    for (c′,x′) in all_subparts(X, Val{c}, x)
      if !D[c′][x′]; set!(c′,x′) end
    end
  end

  for c in ob(S), x in parts(X,c)
    if !D[c][x] && A[c][x] && !B[c][x]; set!(c,x) end
  end
  Subobject(X, D)
end

function common_ob(A::Subobject, B::Subobject)
  (X = ob(A)) == ob(B) ||
    error("Subobjects have different base objects: $(ob(A)) != $(ob(B))")
  return X
end

# FIXME: Should these two accessors go elsewhere?

@generated function all_subparts(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:tuple, map(out_hom(S, c)) do (f,c′)
    :($(quot(c′)), subpart(X,x,$(quot(f))))
  end...)
end

@generated function all_incident(X::StructACSet{S},
                                 ::Type{Val{c}}, x::Int) where {S,c}
  Expr(:call, GlobalRef(Iterators, :flatten),
    Expr(:tuple, map(in_hom(S, c)) do (c′,f)
      :(Tuple{Symbol,Int}[ ($(quot(c′)),x′) for x′ in incident(X,x,$(quot(f))) ])
    end...))
end


# Tensor-hom adjunction (currying of diagrams in C-Set)
#######################################################
const ACSetCat{S} = TypeCat{S, ACSetTransformation}

"""    curry(d::FinFunctor{D, ACSetCat{S}}) where {D,S}
Currying on objects of a functor category
"""
function curry(d::FinFunctor{D, ACSetCat{S}}) where {D,S}
  shapelim = product([dom(d), FinCat(Presentation(S))])
  shape_ind, part_ind = legs(shapelim)
  asl = apex(shapelim)
  omap = Dict(map(ob_generators(asl)) do o
    x = ob_map(shape_ind, o)
    y = ob_map(part_ind, o)
    o => FinSet(ob_map(d, x), Symbol(y))
  end)

  hmap = Dict(map(hom_generators(asl)) do o
    x = hom_map(shape_ind, o)
    y = hom_map(part_ind, o)
    if x isa FreeSchema.Hom{:id}
      o => FinFunction(ob_map(d, only(x.args)), Symbol(y))
    elseif y isa FreeSchema.Hom{:id}
      o => hom_map(d, x)[Symbol(only(y.args))]
    else
      error("x $x y $y")
    end
  end)

  FinDomFunctor(omap,hmap,asl,FinSetCat())
end

"""
Uses an example FinDomFunctor (in the original uncurried format).
"""
function uncurry(d::FinDomFunctor{D1, FinSetCat},
                 old_d::FinDomFunctor{D2, ACSetCat{S}}) where {D1,D2,S}
  # Recover schema for d as a product, not just the apex
  shapelim = product([dom(old_d), FinCat(Presentation(S))])
  asl = apex(shapelim)
  shape_ind, part_ind = legs(shapelim)

  cset_type = typeof(first(old_d.ob_map)[2])
  omap = Dict(map(ob_generators(dom(old_d))) do o
    x = Base.invokelatest(cset_type)
    for o_ in ob_generators(asl)
      if ob_map(shape_ind, o_) == o
        add_parts!(x, Symbol(ob_map(part_ind, o_)), length(ob_map(d, o_)))
      end
    end
    for h in hom_generators(asl)
      h_ = hom_map(shape_ind, h)
      if h_ == id(o)
        set_subpart!(x, Symbol(hom_map(part_ind, h)), collect(hom_map(d, h)))
      end
    end
    o => x
  end)
  hmap = Dict(map(hom_generators(dom(old_d))) do h
    comps = Dict()
    for h_ in hom_generators(asl)
      if hom_map(shape_ind, h_) == h
        comps[Symbol(only(hom_map(part_ind, h_).args))] = hom_map(d, h_)
      end
    end
    dom_, codom_ = [omap[get(h)] for get in [dom, codom]]
    h => ACSetTransformation(dom_,codom_; comps...)
  end)
  FinDomFunctor(omap,hmap,dom(old_d),ACSetCat{S}())
end

"""    curry(d::FinFunctor{D, ACSetCat{S}}) where {D,S}
Currying on morphisms of a functor category with an ACSetCat as codom
"""
function curry(ϕ::FinTransformationMap{D, ACSetCat{S}}) where {D,S}
  cur_d, cur_cd = curry.([dom(ϕ), codom(ϕ)])
  shapelim = product([dom(dom(ϕ)), FinCat(Presentation(S))])
  shape_ind, part_ind = legs(shapelim)
  comps = Dict(map(ob_generators(apex(shapelim))) do o
    oshape, opart = Symbol(shape_ind(o)), Symbol(part_ind(o))
    Symbol(o) => components(ϕ)[oshape][opart]
  end)
  FinTransformationMap(comps,cur_d,cur_cd)
end

"""    uncurry(d::FinTransformationMap, old_d::FinTransformationMap{D, ACSetCat{S}}) where {D, S}
Inverse to currying on morphisms of a functor category with an ACSetCat as codom
"""
function uncurry(d::FinTransformationMap,
                 old_d::FinTransformationMap{D, ACSetCat{S}}) where {D, S}
  # Recover schema for d as a product, not just the apex
  shapelim = product([dom(dom(old_d)), FinCat(Presentation(S))])
  shape_ind, part_ind = legs(shapelim)

  αcomps = Dict(o => DefaultDict{Symbol,Vector{Int}}(()->Int[])
                for o in keys(components(old_d)))

  for o in (ob_generators(apex(shapelim)))
    dic = αcomps[Symbol(ob_map(shape_ind, o))]
    dic[Symbol(ob_map(part_ind, o))] = collect(components(d)[Symbol(o)])
  end

  uc_d, uc_cd = [uncurry(get(d), get(old_d)) for get in [dom, codom]]

  α = Dict(map(collect(αcomps)) do (o, comps)
    o => ACSetTransformation(ob_map(uc_d,   o),
                             ob_map(uc_cd, o); comps...)
  end)


  FinTransformationMap(α, uc_d, uc_cd)
end

# Serialization
###############

""" Serialize an ACSet object to a JSON string
"""
function generate_json_acset(x::T) where T <: ACSet
  ts = tables(x)
  JSON.json(Dict(k => Tables.rowtable(v) for (k,v) in zip(keys(ts),ts)))
end

""" Deserialize a dictionary from a parsed JSON string to an object of the given ACSet type
"""
function parse_json_acset(type::Type{T}, input::Dict) where T <: ACSet
  out = type()
  for (k,v) ∈ input
    add_parts!(out, Symbol(k), length(v))
  end
  for l ∈ values(input)
    for (i, j) ∈ enumerate(l)
      for (k,v) ∈ j
        vtype = eltype(out[Symbol(k)])
        if !(typeof(v) <: vtype)
          v = vtype(v)
        end
        set_subpart!(out, i, Symbol(k), v)
      end
    end
  end
  out
end

""" Deserialize a JSON string to an object of the given ACSet type
"""
function parse_json_acset(type::Type{T}, input::String) where T <: ACSet
  parse_json_acset(type, JSON.parse(input))
end

""" Read a JSON file to an object of the given ACSet type
"""
function read_json_acset(type::Type{T}, input::String) where T <: ACSet
  parse_json_acset(type, open(f->read(f, String), input))
end

""" Serialize an ACSet object to a JSON file
"""
function write_json_acset(x::T, fname::AbstractString) where T <: ACSet
  open(string(fname), "w") do f
    write(f, generate_json_acset(x))
  end
end

end
