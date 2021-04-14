""" Categories of C-sets and attributed C-sets.
"""
module CSets
export ACSetTransformation, CSetTransformation, components, force, is_natural,
  homomorphism, homomorphisms, isomorphism, isomorphisms, migrate!,
  generate_json_acset, parse_json_acset, read_json_acset, write_json_acset

using AutoHashEquals
using JSON
using Reexport
using StaticArrays: SVector

@reexport using ...CSetDataStructures
using ...GAT, ..FreeDiagrams, ..Limits, ..Sets, ..FinSets
import ..Limits: limit, colimit, universal
import ..FinSets: FinSet, FinFunction, FinDomFunction, force
using ...Theories: Category, CatDesc, AttrDesc, ob, hom, attr, adom, acodom
import ...Theories: dom, codom, compose, ⋅, id

# FinSets interop
#################

""" Create `FinSet` for part of attributed C-set.
"""
FinSet(X::ACSet, type::Symbol) = FinSet{Int,Int}(nparts(X, type))

""" Create `FinFunction` for part or subpart of attributed C-set.

The subpart must be of kind `Ob`. For indexed subparts, the index is included.
"""
FinFunction(X::ACSet, name::Symbol) = fin_function(X, Val{name})

@generated function fin_function(X::ACSet{CD,AD,Ts,Idxed},
    ::Type{Val{name}}) where {CD,AD,Ts,Idxed,name}
  if name ∈ ob(CD)
    quote
      FinFunction(identity, FinSet(X, $(QuoteNode(name))))
    end
  elseif name ∈ hom(CD)
    quote
      FinFunction(subpart(X, $(QuoteNode(name))),
                  FinSet(X, $(QuoteNode(codom(CD, name)))),
                  index=$(name ∈ Idxed ? :(X.indices.$name) : false))
    end
  else
    throw(ArgumentError("$(repr(name)) not in $(ob(CD)) or $(hom(CD))"))
  end
end

""" Create `FinDomFunction` for part or subpart of attributed C-set.

The codomain is always of type `TypeSet`, regardless of whether the subpart is
of kind `Ob` or `Data`. For indexed subparts, the index is included.
"""
FinDomFunction(X::ACSet, name::Symbol) = fin_dom_function(X, Val{name})

@generated function fin_dom_function(X::ACSet{CD,AD,Ts,Idxed},
    ::Type{Val{name}}) where {CD,AD,Ts,Idxed,name}
  if name ∈ ob(CD)
    quote
      n = nparts(X, $(QuoteNode(name)))
      FinDomFunction(1:n, FinSet(n), TypeSet{Int}())
    end
  elseif name ∈ hom(CD) || name ∈ attr(AD)
    quote
      FinDomFunction(subpart(X, $(QuoteNode(name))),
                     index=$(name ∈ Idxed ? :(X.indices.$name) : false))
    end
  else
    throw(ArgumentError(
      "$(repr(name)) not in $(ob(CD)), $(hom(CD)), or $(attr(AD))"))
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
@auto_hash_equals struct ACSetTransformation{CD <: CatDesc, AD <: AttrDesc{CD},
    Comp <: NamedTuple, Dom <: AbstractACSet{CD,AD}, Codom <: AbstractACSet{CD,AD}}
  components::Comp
  dom::Dom
  codom::Codom

  function ACSetTransformation{CD,AD}(components::NamedTuple, X::Dom, Y::Codom) where
      {Ob, CD <: CatDesc{Ob}, AD <: AttrDesc{CD},
       Dom <: AbstractACSet{CD,AD}, Codom <: AbstractACSet{CD,AD}}
    @assert keys(components) ⊆ Ob
    coerced_components = NamedTuple{Ob}(
      coerce_component(ob, get(components, ob) do; Int[] end, X, Y)
      for ob in Ob)
    new{CD,AD,typeof(coerced_components),Dom,Codom}(coerced_components, X, Y)
  end
end

function coerce_component(ob::Symbol, f::FinFunction{Int,Int}, X, Y)
  @assert length(dom(f)) == nparts(X,ob) "Domain error in component $ob"
  @assert length(codom(f)) == nparts(Y,ob) "Codomain error in component $ob"
  return f
end
function coerce_component(ob::Symbol, f, X, Y)::FinFunction{Int,Int}
  FinFunction(f, nparts(X,ob), nparts(Y,ob))
end

ACSetTransformation(components, X::Dom, Y::Codom) where
    {CD, AD, Dom <: AbstractACSet{CD,AD}, Codom <: AbstractACSet{CD,AD}} =
  ACSetTransformation{CD,AD}(components, X, Y)
ACSetTransformation(X::Dom, Y::Codom; components...) where
    {CD, AD, Dom <: AbstractACSet{CD,AD}, Codom <: AbstractACSet{CD,AD}} =
  ACSetTransformation{CD,AD}((; components...), X, Y)

const CSetTransformation{CD, Comp,
                         Dom <: AbstractCSet{CD}, Codom <: AbstractCSet{CD}} =
  ACSetTransformation{CD,AttrDesc{CD,(),(),(),()},Comp,Dom,Codom}

CSetTransformation(components, X::AbstractCSet, Y::AbstractCSet) =
  ACSetTransformation(components, X, Y)
CSetTransformation(X::AbstractCSet, Y::AbstractCSet; components...) =
  ACSetTransformation(X, Y; components...)

components(α::ACSetTransformation) = α.components
Base.getindex(α::ACSetTransformation, ob) = α.components[ob]

""" Is the transformation between C-sets a natural transformation?

Uses the fact that to check whether a transformation is natural, it suffices to
check the naturality equation on a generating set of morphisms.
"""
function is_natural(α::ACSetTransformation{CD,AD}) where {CD,AD}
  X, Y = dom(α), codom(α)
  for (f, c, d) in zip(hom(CD), dom(CD), codom(CD))
    Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
    all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf)) || return false
  end
  for (f, c) in zip(attr(AD), adom(AD))
    Xf, Yf, α_c = subpart(X,f), subpart(Y,f), α[c]
    all(Yf[α_c(i)] == Xf[i] for i in eachindex(Xf)) || return false
  end
  return true
end

force(α::ACSetTransformation) =
  ACSetTransformation(map(force, components(α)), dom(α), codom(α))

# Finding C-set transformations
###############################

""" Find a homomorphism between two attributed ``C``-sets.

Returns `nothing` if no homomorphism exists. For many categories ``C``, the
``C``-set homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.

This procedure uses the classic backtracking search algorithm for a
combinatorial constraint satisfaction problem (CSP). As is well known, the
homomorphism problem for relational databases is equivalent to CSP. Since the
C-set homomorphism problem is "the same" as the database homomorphism problem
(insofar as attributed C-sets are "the same" as relational databases), it is
also equivalent to CSP. Backtracking search for CSP is described in many
computer science textbooks, such as (Russell & Norvig 2010, *Artificial
Intelligence*, Third Ed., Chapter 6: Constraint satisfaction problems, esp.
Algorithm 6.5). In our implementation, the search tree is ordered using the
popular heuristic of "minimum remaining values" (MRV), also known as "most
constrained variable."

Set the keyword argument `monic=true` to restrict to monomorphisms:
homomorphisms whose components are all injective functions.

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
function homomorphism(X::AbstractACSet, Y::AbstractACSet; monic::Bool=false)
  result = backtracking_search(X, Y, findall=false, monic=monic)
  isnothing(result) ? nothing : ACSetTransformation(result, X, Y)
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
function homomorphisms(X::AbstractACSet, Y::AbstractACSet; monic::Bool=false)
  results = backtracking_search(X, Y, findall=true, monic=monic)
  map(components -> ACSetTransformation(components, X, Y), results)
end

""" Find an isomorphism between two attributed ``C``-sets, if one exists.

See [`homomorphism`](@ref) for more information about the algorithms involved.
"""
function isomorphism(X::AbstractACSet, Y::AbstractACSet)
  result = backtracking_search(X, Y, findall=false, iso=true)
  isnothing(result) ? nothing : ACSetTransformation(result, X, Y)
end

""" Find all isomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`isomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
function isomorphisms(X::AbstractACSet, Y::AbstractACSet)
  results = backtracking_search(X, Y, findall=true, iso=true)
  map(components -> ACSetTransformation(components, X, Y), results)
end

""" Internal state for backtracking search for ACSet homomorphisms.
"""
struct BacktrackingState{CD <: CatDesc, AD <: AttrDesc{CD},
    Assign <: NamedTuple, Dom <: AbstractACSet{CD,AD}, Codom <: AbstractACSet{CD,AD}}
  """ The current assignment, a partially-defined homomorphism of ACSets. """
  assignment::Assign
  """ Depth in search tree at which assignments were made. """
  assignment_depth::Assign
  """ Inverse assignment if finding a monomorphism, otherwise `nothing`. """
  inv_assignment::Union{Nothing,Assign}
  """ Domain ACSet: the "variables" in the CSP. """
  dom::Dom
  """ Codomain ACSet: the "values" in the CSP. """
  codom::Codom
  """ List of completed assignments if finding all homomorphisms;
  always `nothing` if finding one homomorphism.
  """
  results::Union{Nothing,Vector{Assign}}
end

function backtracking_search(X::AbstractACSet{CD}, Y::AbstractACSet{CD};
                             monic::Bool=false, iso::Bool=false,
                             findall::Bool=false) where {Ob, CD<:CatDesc{Ob}}
  # Fail early if no monic/iso exists on cardinality grounds.
  Assign = NamedTuple{Ob,Tuple{(Vector{Int} for c in Ob)...}}
  results = findall ? Assign[] : nothing
  if iso
    all(nparts(X,c) == nparts(Y,c) for c in Ob) || return results
    # Injections between finite sets are bijections, so reduce to that case.
    monic = true
  elseif monic
    all(nparts(X,c) <= nparts(Y,c) for c in Ob) || return results
  end

  assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
  assignment_depth = map(copy, assignment)
  inv_assignment = monic ?
    NamedTuple{Ob}(zeros(Int, nparts(Y, c)) for c in Ob) : nothing
  state = BacktrackingState(assignment, assignment_depth, inv_assignment,
                            X, Y, results)
  backtracking_search(state, 0)
end

function backtracking_search(state::BacktrackingState, depth::Int)
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    return isnothing(state.results) ? state.assignment :
      push!(state.results, map(copy, state.assignment))
  elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return state.results
  end
  c, x = mrv_elem

  # Attempt all assignments of the chosen element.
  Y = state.codom
  for y in parts(Y, c)
    if assign_elem!(state, depth, c, x, y)
      result = backtracking_search(state, depth + 1)
      if isnothing(state.results) && !isnothing(result)
        return result
      end
    end
    unassign_elem!(state, depth, c, x)
  end
  state.results
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState{CD}, depth) where CD
  mrv, mrv_elem = Inf, nothing
  Y = state.codom
  for c in ob(CD), (x, y) in enumerate(state.assignment[c])
    y == 0 || continue
    n = count(can_assign_elem(state, depth, c, x, y) for y in parts(Y, c))
    if n < mrv
      mrv, mrv_elem = n, (c, x)
    end
  end
  (mrv, mrv_elem)
end

""" Check whether element (c,x) can be assigned to (c,y) in current assignment.
"""
function can_assign_elem(state::BacktrackingState, depth, c, x, y)
  # Although this method is nonmutating overall, we must temporarily mutate the
  # backtracking state, for several reasons. First, an assignment can be a
  # consistent at each individual subpart but not consistent for all subparts
  # simultaneously (consider trying to assign a self-loop to an edge with
  # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
  # must keep track of which elements we have visited to avoid looping forever.
  ok = assign_elem!(state, depth, c, x, y)
  unassign_elem!(state, depth, c, x)
  return ok
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.

Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""
function assign_elem!(state::BacktrackingState{CD,AD}, depth, c, x, y) where {CD, AD}
  y′ = state.assignment[c][x]
  y′ == y && return true  # If x is already assigned to y, return immediately.
  y′ == 0 || return false # Otherwise, x must be unassigned.
  if !isnothing(state.inv_assignment) && state.inv_assignment[c][y] != 0
    # Also, y must unassigned in the inverse assignment.
    return false
  end

  # Check attributes first to fail as quickly as possible.
  X, Y = state.dom, state.codom
  for f in out_attr(AD, Val{c})
    subpart(X,x,f) == subpart(Y,y,f) || return false
  end

  # Make the assignment and recursively assign subparts.
  state.assignment[c][x] = y
  state.assignment_depth[c][x] = depth
  if !isnothing(state.inv_assignment)
    state.inv_assignment[c][y] = x
  end
  for (f, d) in out_hom(CD, Val{c})
    assign_elem!(state, depth, d,
                 subpart(X,x,f), subpart(Y,y,f)) || return false
  end
  return true
end

""" Unassign the element (c,x) in the current assignment.
"""
function unassign_elem!(state::BacktrackingState{CD}, depth, c, x) where CD
  state.assignment[c][x] == 0 && return
  assign_depth = state.assignment_depth[c][x]
  @assert assign_depth <= depth
  if assign_depth == depth
    X = state.dom
    if !isnothing(state.inv_assignment)
      y = state.assignment[c][x]
      state.inv_assignment[c][y] = 0
    end
    state.assignment[c][x] = 0
    state.assignment_depth[c][x] = 0
    for (f, d) in out_hom(CD, Val{c})
      unassign_elem!(state, depth, d, subpart(X,x,f))
    end
  end
end

@generated function out_hom(::Type{CD}, ::Type{Val{c}}) where {CD<:CatDesc, c}
  Expr(:tuple, (:($(QuoteNode(f)) => $(QuoteNode(codom(CD, f))))
                for f in hom(CD) if dom(CD, f) == c)...)
end
@generated function out_attr(::Type{AD}, ::Type{Val{c}}) where {AD<:AttrDesc, c}
  Expr(:tuple, (QuoteNode(f) for f in attr(AD) if dom(AD, f) == c)...)
end

# Category of C-sets
####################

@instance Category{ACSet, ACSetTransformation} begin
  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::ACSet) = ACSetTransformation(map(id, fin_sets(X)), X, X)

  function compose(α::ACSetTransformation, β::ACSetTransformation)
    # Question: Should we incur cost of checking that codom(β) == dom(α)?
    ACSetTransformation(map(compose, components(α), components(β)),
                        dom(α), codom(β))
  end
end

fin_sets(X::ACSet) = map(table -> FinSet(length(table)), tables(X))

# Limits and colimits
#####################

""" Limit of C-sets that stores the pointwise limits in FinSet.
"""
struct CSetLimit{Ob <: AbstractCSet, Diagram, Cone <: Multispan{Ob},
                 Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

""" Colimit of attributed C-sets that stores the pointwise colimits in FinSet.
"""
struct ACSetColimit{Ob <: AbstractACSet, Diagram, Cocone <: Multicospan{Ob},
                    Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

# Compute limits and colimits of C-sets by reducing to those in FinSet using the
# "pointwise" formula for (co)limits in functor categories.

function limit(diagram::AbstractFreeDiagram{ACS}) where
    {CD <: CatDesc, ACS <: AbstractCSet{CD}}
  limits = map(limit, unpack_diagram(diagram))
  Xs = cone_objects(diagram)
  Y = ACS()
  for (c, lim) in pairs(limits)
    add_parts!(Y, c, length(ob(lim)))
  end
  for (f, c, d) in zip(hom(CD), dom(CD), codom(CD))
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

function colimit(diagram::AbstractFreeDiagram{ACS}) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts, ACS <: AbstractACSet{CD,AD,Ts}}
  # Colimit of C-set without attributes.
  colimits = map(colimit, unpack_diagram(diagram))
  Xs = cocone_objects(diagram)
  Y = ACS()
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in zip(hom(CD), dom(CD), codom(CD))
    Yfs = map(legs(colimits[d]), Xs) do ι, X
      compose(FinFunction(subpart(X, f), nparts(X, d)), ι)
    end
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs))

  # Set data attributes by canonical inclusion from attributes in diagram.
  for (attr, c, d) in zip(attr(AD), adom(AD), acodom(AD))
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
unpack_diagram(discrete::DiscreteDiagram{<:AbstractACSet}) =
  map(DiscreteDiagram, unpack_sets(ob(discrete)))
unpack_diagram(span::Multispan{<:AbstractACSet}) =
  map(Multispan, fin_sets(apex(span)), unpack_components(legs(span)))
unpack_diagram(cospan::Multicospan{<:AbstractACSet}) =
  map(Multicospan, fin_sets(apex(cospan)), unpack_components(legs(cospan)))
unpack_diagram(para::ParallelMorphisms{<:AbstractACSet}) =
  map(ParallelMorphisms, unpack_components(hom(para)))

function unpack_diagram(d::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}}) where
    {Ob, CD <: CatDesc{Ob}, ACS <: AbstractACSet{CD}}
  NamedTuple{Ob}([ map(d, Ob=X -> FinSet(X, ob), Hom=α -> α[ob]) for ob in Ob ])
end

""" Vector of C-sets → named tuple of vectors of FinSets
"""
unpack_sets(Xs::AbstractVector{<:AbstractACSet{CD}}) where
    {Ob, CD <: CatDesc{Ob}} =
  NamedTuple{Ob}([ map(X -> FinSet(X, ob), Xs) for ob in Ob ])

""" Vector of C-set transformations → named tuple of vectors of FinFunctions
"""
unpack_components(αs::AbstractVector{<:ACSetTransformation{CD}}) where
    {Ob, CD <: CatDesc{Ob}} =
  NamedTuple{Ob}([ map(α -> α[ob], αs) for ob in Ob ])

""" Named tuple of vectors of FinFunctions → vector of C-set transformations
"""
function pack_components(fs::NamedTuple{Ob}, doms, codoms) where Ob
  components = map((x...) -> NamedTuple{Ob}(x), fs...) # XXX: Is there a better way?
  map(ACSetTransformation, components, doms, codoms)
end

""" Objects in diagram that will have explicit legs in limit cone.

Encodes common conventions such as, when taking a pullback of a cospan, not
explicitly including a cone leg for the cospan apex since it can be computed
from the other legs.

FIXME: Should this function be part of the official limits interface?
"""
cone_objects(diagram) = ob(diagram)
cone_objects(diagram::BipartiteFreeDiagram) = ob₁(diagram)
cone_objects(cospan::Multicospan) = feet(cospan)
cone_objects(para::ParallelMorphisms) = SVector(dom(para))

""" Objects in diagram that will have explicit legs in colimit cocone.
"""
cocone_objects(diagram) = ob(diagram)
cocone_objects(diagram::BipartiteFreeDiagram) = ob₂(diagram)
cocone_objects(span::Multispan) = feet(span)
cocone_objects(para::ParallelMorphisms) = SVector(codom(para))

# Functorial data migration
###########################

""" Pullback functorial data migration from one ACSet to another.

Note that this operation is contravariant: the data is transferred from `X` to
`Y` but the functor, represented by two dictionaries, maps the schema for `Y`
to the schema for `X`.

When the functor is the identity, this function is equivalent to
[`copy_parts!`](@ref).
"""
function migrate!(Y::ACSet{CD, AD}, X::ACSet,
                  FOb::AbstractDict, FHom::AbstractDict) where {CD, AD}
  ob(CD) ⊆ keys(FOb)     || error("Every object in $CD must be a key in $FOb")
  hom(CD) ⊆ keys(FHom)   || error("Every morphism in $CD must be a key in $FHom")
  attr(AD) ⊆ keys(FHom)  || error("Every attribute in $AD must be a key in $FHom")
  
  partsY = NamedTuple{ob(CD)}(map(ob(CD)) do obY
    add_parts!(Y, obY, nparts(X, FOb[obY]))
  end)
  for homY in hom(CD)
    domY, codomY = dom(CD, homY), codom(CD, homY)
    set_subpart!(Y, partsY[domY], homY, partsY[codomY][subpart(X, FHom[homY])])
  end
  for attrY in attr(AD)
    domY = dom(AD, attrY)
    set_subpart!(Y, partsY[domY], attrY, subpart(X, FHom[attrY]))
  end
  return Y
end

function (::Type{T})(X::ACSet, FOb::AbstractDict,
                     FHom::AbstractDict) where T <: AbstractACSet
  Y = T()
  migrate!(Y, X, FOb, FHom)
end

""" Serialize an ACSet object to a JSON string
"""
function generate_json_acset(x::T) where T <: AbstractACSet
  JSON.json(x.tables)
end

""" Deserialize a dictionary from a parsed JSON string to an object of the given ACSet type
"""
function parse_json_acset(type::Type{T}, input::Dict) where T <: AbstractACSet
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
function parse_json_acset(type::Type{T}, input::String) where T <: AbstractACSet
  parse_json_acset(type, JSON.parse(input))
end

""" Read a JSON file to an object of the given ACSet type
"""
function read_json_acset(type::Type{T}, input::String) where T <: AbstractACSet
  parse_json_acset(type, open(f->read(f, String), input))
end

""" Serialize an ACSet object to a JSON file
"""
function write_json_acset(x::T, fname::AbstractString) where T <: AbstractACSet
  open(string(fname), "w") do f
    write(f, generate_json_acset(x))
  end
end

end
