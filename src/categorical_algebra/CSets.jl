""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetTransformation, CSetTransformation, SubACSet, SubCSet,
  components, force, is_natural, homomorphism, homomorphisms, is_homomorphic,
  isomorphism, isomorphisms, is_isomorphic,
  generate_json_acset, parse_json_acset, read_json_acset, write_json_acset

using Base.Meta: quot
using AutoHashEquals
using JSON
using Reexport
using Tables

@reexport using ...CSetDataStructures
using ...GAT, ..FreeDiagrams, ..Limits, ..Subobjects, ..Sets, ..FinSets
import ..Limits: limit, colimit, universal, pushout_complement,
  can_pushout_complement
import ..Subobjects: Subobject, SubobjectBiHeytingAlgebra,
  implies, ⟹, subtract, \, negate, ¬, non, ~
import ..FinSets: FinSet, FinFunction, FinDomFunction, force, predicate
using ...Theories: SchemaDescType, CSetSchemaDescType, Category,
  attr, adom, acodom, acodom_nums
import ...Theories: dom, codom, compose, ⋅, id,
  ob, hom, meet, ∧, join, ∨, top, ⊤, bottom, ⊥

# FinSets interop
#################

""" Create `FinSet` for part of attributed C-set.
"""
FinSet(X::StructACSet, type::Symbol) = FinSet{Int,Int}(nparts(X, type))

""" Create `FinFunction` for part or subpart of attributed C-set.

The subpart must be of kind `Ob`. For indexed subparts, the index is included.
"""
FinFunction(X::StructACSet, name::Symbol) = fin_function(X, Val{name})

@generated function fin_function(X::StructACSet{S,Ts,Idxed},
    ::Type{Val{name}}) where {Ts,S,Idxed,name}
  if name ∈ ob(S)
    quote
      FinFunction(identity, FinSet(X, $(QuoteNode(name))))
    end
  elseif name ∈ hom(S)
    quote
      FinFunction(subpart(X, $(QuoteNode(name))),
                  FinSet(X, $(QuoteNode(codom(S, name)))),
                  index=$(Idxed[name] ? :(X.hom_indices.$name) : false))
    end
  else
    throw(ArgumentError("$(repr(name)) not in $(ob(S)) or $(hom(S))"))
  end
end

""" Create `FinDomFunction` for part or subpart of attributed C-set.

The codomain is always of type `TypeSet`, regardless of whether the subpart is
of kind `Ob` or `Data`. For indexed subparts, the index is included.
"""
FinDomFunction(X::StructACSet, name::Symbol) = fin_dom_function(X, Val{name})

@generated function fin_dom_function(X::StructACSet{S,Ts,Idxed},
    ::Type{Val{name}}) where {S,Ts,Idxed,name}
  if name ∈ ob(S)
    quote
      n = nparts(X, $(QuoteNode(name)))
      FinDomFunction(1:n, FinSet(n), TypeSet{Int}())
    end
  elseif name ∈ hom(S) || name ∈ attr(S)
    index_name = name ∈ hom(S) ? :hom_indices : :attr_indices
    quote
      FinDomFunction(subpart(X, $(QuoteNode(name))),
                     index=$(Idxed[name] ? :(X.$index_name.$name) : false))
    end
  else
    throw(ArgumentError(
      "$(repr(name)) not in $(ob(S)), $(hom(S)), or $(attr(S))"))
  end
end

# C-set transformations
#######################

""" Transformation between attributed C-sets.

A homomorphism of C-sets is a natural transformation: a transformation between
functors C → Set satisfying the naturality axiom for all morphisms in C. This
struct records the data of a transformation; it does not enforce naturality, but
see [`is_natural`](@ref).

A C-set transformation has a component for every object in C. When C-sets have
attributes, the data types are assumed to be fixed. Thus, the naturality axiom
for data attributes is a commutative triangle, rather than a commutative square.
"""
@auto_hash_equals struct ACSetTransformation{S, Comp <: NamedTuple,
                                             Dom <: StructACSet{S}, Codom <: StructACSet{S}}
  components::Comp
  dom::Dom
  codom::Codom
  function ACSetTransformation{S}(components::NamedTuple, X::Dom, Y::Codom) where
      {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}}
    @assert keys(components) ⊆ ob(S)
    coerced_components = NamedTuple{Tuple(ob(S))}(
      coerce_component(ob, get(components, ob) do; 1:0 end, X, Y)
      for ob in ob(S))
    new{S,typeof(coerced_components),Dom,Codom}(coerced_components, X, Y)
  end
end

function coerce_component(ob::Symbol, f::FinFunction{Int,Int}, X, Y)
  length(dom(f)) == nparts(X,ob) || error("Domain error in component $ob")
  length(codom(f)) == nparts(Y,ob) || error("Codomain error in component $ob")
  return f
end
function coerce_component(ob::Symbol, f, X, Y)::FinFunction{Int,Int}
  FinFunction(f, nparts(X,ob), nparts(Y,ob))
end

ACSetTransformation(components, X::Dom, Y::Codom) where
    {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}} =
  ACSetTransformation{S}(components, X, Y)
ACSetTransformation(X::Dom, Y::Codom; components...) where
    {S, Dom <: StructACSet{S}, Codom <: StructACSet{S}} =
  ACSetTransformation{S}((; components...), X, Y)

const CSetTransformation{S<:CSetSchemaDescType, Comp,
                         Dom <: StructCSet{S}, Codom <: StructCSet{S}} =
  ACSetTransformation{S,Comp,Dom,Codom}

CSetTransformation(components, X::StructCSet, Y::StructCSet) =
  ACSetTransformation(components, X, Y)
CSetTransformation(X::StructCSet, Y::StructCSet; components...) =
  ACSetTransformation(X, Y; components...)

components(α::ACSetTransformation) = α.components
Base.getindex(α::ACSetTransformation, ob) = α.components[ob]

""" Is the transformation between C-sets a natural transformation?

Uses the fact that to check whether a transformation is natural, it suffices to
check the naturality equation on a generating set of morphisms.
"""
function is_natural(α::ACSetTransformation{S}) where {S}
  X, Y = dom(α), codom(α)
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
    all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf)) || return false
  end
  for (f, c) in zip(attr(S), adom(S))
    Xf, Yf, α_c = subpart(X,f), subpart(Y,f), α[c]
    all(Yf[α_c(i)] == Xf[i] for i in eachindex(Xf)) || return false
  end
  return true
end

map_components(f, α::ACSetTransformation) =
  ACSetTransformation(map(f, components(α)), dom(α), codom(α))
force(α::ACSetTransformation) = map_components(force, α)

# Finding C-set transformations
###############################

""" Find a homomorphism between two attributed ``C``-sets.

Returns `nothing` if no homomorphism exists. For many categories ``C``, the
``C``-set homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.

This procedure uses the classic backtracking search algorithm for a
combinatorial constraint satisfaction problem (CSP). As is well known, the
homomorphism problem for relational databases is reducible to CSP. Since the
C-set homomorphism problem is "the same" as the database homomorphism problem
(insofar as attributed C-sets are "the same" as relational databases), it is
also reducible to CSP. Backtracking search for CSP is described in many computer
science textbooks, such as (Russell & Norvig 2010, *Artificial Intelligence*,
Third Ed., Chapter 6: Constraint satisfaction problems, esp. Algorithm 6.5). In
our implementation, the search tree is ordered using the popular heuristic of
"minimum remaining values" (MRV), also known as "most constrained variable."

To restrict to *monomorphisms*, or homomorphisms whose components are all
injective functions, set the keyword argument `monic=true`. To restrict only
certain components to be injective or bijective, use `monic=[...]` or
`iso=[...]`. For example, setting `monic=[:V]` for a graph homomorphism ensures
that the vertex map is injective but imposes no constraints on the edge map.

To restrict the homomorphism to a given partial assignment, set the keyword
argument `initial`. For example, to fix the first source vertex to the third
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`.

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
  result = nothing
  homomorphisms(X, Y; kw...) do α
    result = α; return true
  end
  result
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S};
                       kw...) where {S}
  results = ACSetTransformation{S}[]
  homomorphisms(X, Y; kw...) do α
    push!(results, map_components(deepcopy, α)); return false
  end
  results
end
homomorphisms(f, X::StructACSet, Y::StructACSet;
              monic=false, iso=false, initial=(;)) =
  backtracking_search(f, X, Y, monic=monic, iso=iso, initial=initial)

""" Is the first attributed ``C``-set homomorphic to the second?

A convenience function based on [`homomorphism`](@ref).
"""
is_homomorphic(X::StructACSet, Y::StructACSet; kw...) =
  !isnothing(homomorphism(X, Y; kw...))

""" Find an isomorphism between two attributed ``C``-sets, if one exists.

See [`homomorphism`](@ref) for more information about the algorithms involved.
"""
isomorphism(X::StructACSet, Y::StructACSet; initial=(;)) =
  homomorphism(X, Y, iso=true, initial=initial)

""" Find all isomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`isomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
isomorphisms(X::StructACSet, Y::StructACSet; initial=(;)) =
  homomorphisms(X, Y, iso=true, initial=initial)
isomorphisms(f, X::StructACSet, Y::StructACSet; initial=(;)) =
  homomorphisms(f, X, Y, iso=true, initial=initial)

""" Are the two attributed ``C``-sets isomorphic?

A convenience function based on [`isomorphism`](@ref).
"""
is_isomorphic(X::StructACSet, Y::StructACSet; kw...) =
  !isnothing(isomorphism(X, Y; kw...))

""" Internal state for backtracking search for ACSet homomorphisms.
"""
struct BacktrackingState{S <: SchemaDescType,
    Assign <: NamedTuple, PartialAssign <: NamedTuple,
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
end

function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
                             monic=false, iso=false, initial=(;)) where {Ob, S<:SchemaDescType{Ob}}
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
  state = BacktrackingState(assignment, assignment_depth, inv_assignment, X, Y)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments)
      assign_elem!(state, 0, Val{c}, x, y) || return false
    end
  end

  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1)
end

function backtracking_search(f, state::BacktrackingState, depth::Int)
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    return f(ACSetTransformation(state.assignment, state.dom, state.codom))
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
    $(map(out_attr(S, c)) do f
        :(subpart(X,x,$(quot(f))) == subpart(Y,y,$(quot(f))) || return false)
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
out_attr(S, c) = [f for f in attr(S) if dom(S, f) == c]

# Category of C-sets
####################

@instance Category{StructACSet, ACSetTransformation} begin
  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::StructACSet) = ACSetTransformation(map(id, fin_sets(X)), X, X)

  function compose(α::ACSetTransformation, β::ACSetTransformation)
    # Question: Should we incur cost of checking that codom(β) == dom(α)?
    ACSetTransformation(map(compose, components(α), components(β)),
                        dom(α), codom(β))
  end
end

fin_sets(X::StructACSet{S}) where {S} = NamedTuple(A => FinSet(nparts(X,A)) for A in ob(S))

@cartesian_monoidal_instance ACSet ACSetTransformation
@cocartesian_monoidal_instance ACSet ACSetTransformation

# Limits and colimits
#####################

""" Limit of C-sets that stores the pointwise limits in FinSet.
"""
struct CSetLimit{Ob <: StructCSet, Diagram, Cone <: Multispan{Ob},
                 Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

""" Colimit of attributed C-sets that stores the pointwise colimits in FinSet.
"""
struct ACSetColimit{Ob <: StructACSet, Diagram, Cocone <: Multicospan{Ob},
                    Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

# Compute limits and colimits of C-sets by reducing to those in FinSet using the
# "pointwise" formula for (co)limits in functor categories.

function limit(::Type{ACS}, diagram) where
    {S <: CSetSchemaDescType, ACS <: StructCSet{S}}
  limits = map(limit, unpack_diagram(diagram))
  Xs = cone_objects(diagram)
  Y = ACS()
  for (c, lim) in pairs(limits)
    add_parts!(Y, c, length(ob(lim)))
  end
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Yfs = map(legs(limits[c]), Xs) do π, X
      compose(π, FinFunction(subpart(X, f), nparts(X, d)))
    end
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  πs = pack_components(map(legs, limits), map(X -> Y, Xs), Xs)
  CSetLimit(diagram, Multispan(Y, πs), limits)
end

function universal(lim::CSetLimit, cone::Multispan)
  components = map(universal, lim.limits, unpack_diagram(cone))
  CSetTransformation(components, apex(cone), ob(lim))
end

function colimit(::Type{ACS}, diagram) where {S, Ts, ACS <: StructACSet{S,Ts}}
  # Colimit of C-set without attributes.
  colimits = map(colimit, unpack_diagram(diagram))
  Xs = cocone_objects(diagram)
  Y = ACS()
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Yfs = map(legs(colimits[d]), Xs) do ι, X
      compose(FinFunction(subpart(X, f), nparts(X, d)), ι)
    end
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

""" Diagram in C-Set → named tuple of diagrams in FinSet
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet}) =
  map(DiscreteDiagram, unpack_sets(ob(discrete)))
unpack_diagram(span::Multispan{<:ACSet}) =
  map(Multispan, fin_sets(apex(span)), unpack_components(legs(span)))
unpack_diagram(cospan::Multicospan{<:ACSet}) =
  map(Multicospan, fin_sets(apex(cospan)), unpack_components(legs(cospan)))
unpack_diagram(para::ParallelMorphisms{<:ACSet}) =
  map(ParallelMorphisms, unpack_components(hom(para)))
unpack_diagram(comp::ComposableMorphisms{<:ACSet}) =
  map(ComposableMorphisms, unpack_components(hom(comp)))

function unpack_diagram(d::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}}) where
    {Ob, S <: SchemaDescType{Ob}, ACS <: StructACSet{S}}
  NamedTuple{Ob}([ map(d, Ob=X -> FinSet(X, ob), Hom=α -> α[ob]) for ob in Ob ])
end

""" Vector of C-sets → named tuple of vectors of FinSets
"""
unpack_sets(Xs::AbstractVector{<:StructACSet{S}}) where
    {Ob, S <: SchemaDescType{Ob}} =
  NamedTuple{Ob}([ map(X -> FinSet(X, ob), Xs) for ob in Ob ])

""" Vector of C-set transformations → named tuple of vectors of FinFunctions
"""
unpack_components(αs::AbstractVector{<:ACSetTransformation{S}}) where
    {Ob, S <: SchemaDescType{Ob}} =
  NamedTuple{Ob}([ map(α -> α[ob], αs) for ob in Ob ])

""" Named tuple of vectors of FinFunctions → vector of C-set transformations
"""
function pack_components(fs::NamedTuple{Ob}, doms, codoms) where Ob
  components = map((x...) -> NamedTuple{Ob}(x), fs...) # XXX: Is there a better way?
  map(ACSetTransformation, components, doms, codoms)
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
    sets = fin_sets(X)
    @assert keys(components) ⊆ keys(sets)
    coerced_components = NamedTuple{keys(sets)}(
      coerce_subob_component(set, get(components, ob) do; 1:0 end)
      for (ob, set) in pairs(sets))
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
  Subobject(X, map(X₀ -> top(X₀, SubOpBoolean()), fin_sets(X)))
bottom(X::ACSet, ::SubOpBoolean) =
  Subobject(X, map(X₀ -> bottom(X₀, SubOpBoolean()), fin_sets(X)))

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
  D = map(X₀ -> trues(length(X₀)), fin_sets(X))

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
  D = map(X₀ -> falses(length(X₀)), fin_sets(X))

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
