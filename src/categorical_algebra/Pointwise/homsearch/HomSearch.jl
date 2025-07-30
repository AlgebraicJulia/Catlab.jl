export ACSetHomomorphismAlgorithm, BacktrackingSearch, HomomorphismQuery,
       homomorphism, homomorphisms, is_homomorphic,
       isomorphism, isomorphisms, is_isomorphic,
       @acset_transformation, @acset_transformations
   

using Random, StructEquality
using CompTime
using MLStyle: @match

using ACSets.DenseACSets: attrtype_type

using ....Graphs.BasicGraphs
using ....Theories, ....BasicSets, ...Cats, ...SetCats
using ..ACSetTransformations, ..CSets
using ..ACSetTransformations: map_components

# Finding C-set transformations
###############################

""" Algorithm for finding homomorphisms between attributed ``C``-sets."""
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

""" Find a unique homomorphism between two attributed ``C``-sets (subject to a
variety of constraints), if one exists.

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
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`. Use the
keyword argument `type_components` to specify nontrivial components on attribute
types for a loose homomorphism. These components must be callable: either Julia
functions on the appropriate types or FinFunction(Dict(...)).

Use the keyword argument `alg` to set the homomorphism-finding algorithm. By
default, a backtracking search algorithm is used ([`BacktrackingSearch`](@ref)).
Use the keyword argument error_failures = true to get errors explaining any
immediate inconsistencies in specified initial data.

The keyword `predicates` accepts a Dict{Ob, Dict{Int, Union{Nothing,
AbstractVector{Int}}}} For each part of the domain, we have the option to give a
constraint as a boolean function of the current assignment and tentative value
to assign. E.g. `predicates = (E = Dict(2 => [2,4,6]))` would only find matches
which assigned edge#2 to edge #2, #4, or #6 in the codomain.

The keyword `no_bind` can be a boolean (applying to all AttrTypes) or an
iterable of specific components: it prevents attribute variables in the domain
from being sent to concrete values in the codomain. When the AttrType component
is `monic`, it is also the case that attribute variables cannot be sent to
concrete values (therefore it is redundant to set `no_bind=true` in such cases).
In both of these cases, it's possible to compute homomorphisms when there are
"free-floating" attribute variables (which are not referred to by any Attr in
the domain), as each such variable has a finite number of possibilities for it
to be mapped to.

Setting `any=true` relaxes the constraint that the returned homomorphism is 
unique.

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; any=false, kw...)
  res = homomorphisms(X, Y, alg; Dict((any ? :take : :max) => 1)..., kw...)
  isempty(res) ? nothing : only(res)
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
homomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphisms(X, Y, alg; kw...)

""" Find all homomorphisms between two attributed ``C``-sets via BackTracking Search.

take = number of homomorphisms requested (stop the search process early if this 
       number is reached)
max = throw an error if we take more than this many morphisms (e.g. set max=1 if 
      one expects 0 or 1 morphism)
filter = only consider morphisms which meet some criteria, expressed as a Julia 
         function of type ACSetTransformation -> Bool

It does not make sense to specify both `take` and `max`.
"""
function homomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; 
                       take=nothing, max=nothing, filter=nothing, kw...) 
  results = []
  isnothing(take) || isnothing(max) || error(
    "Cannot set both `take`=$take and `max`=$max for `homomorphisms`")
  backtracking_search(X, Y; kw...) do αs
    for α in αs
      isnothing(filter) || filter(α) || continue
      length(results) == max && error("Exceeded $max: $([results; α])")
      push!(results, map_components(deepcopy, α));
      length(results) == take && return true
    end 
    return false
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
  !isempty(homomorphisms(X, Y, alg; take=1, kw...))

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

isomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;), kw...) =
  homomorphisms(X, Y, alg; iso=true, initial=initial, kw...)

""" Are the two attributed ``C``-sets isomorphic?

This function generally reduces to [`isomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_isomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_isomorphic(X, Y, alg; kw...)

is_isomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isempty(isomorphisms(X, Y, alg; take=1, kw...))

# Backtracking search
#--------------------

""" Get assignment pairs from partially specified component of C-set morphism.
"""
partial_assignments(x::FinFunction; is_attr=false) = partial_assignments(collect(x))
partial_assignments(x::AbstractDict; is_attr=false) = pairs(x)
partial_assignments(x::AbstractVector; is_attr=false) =
  ((i,y) for (i,y) in enumerate(x) if is_attr || (!isnothing(y) && y > 0))


""" Internal state for backtracking search for ACSet homomorphisms.

Assignment of attribute variables maintains both the assignment as well as the 
number of times that variable has been bound. We can only *freely* assign the 
variable to match any AttrVar or concrete attribute value if it has not yet 
been bound.
"""
struct BacktrackingState{
  Dom <: ACSet, Codom <: ACSet,
  Assign <: NamedTuple, PartialAssign <: NamedTuple, LooseFun <: NamedTuple,
  Predicates <: NamedTuple,Image <: NamedTuple, Unassign<: NamedTuple
  }
  assignment::Assign
  assignment_depth::Assign
  inv_assignment::PartialAssign
  dom::Dom
  codom::Codom
  type_components::LooseFun
  predicates::Predicates
  image::Image # Negative of image for epic components or if finding an epimorphism
  unassigned::Unassign # "# of unassigned elems in domain of a component 
end

function backtracking_search(f, X::ACSet, Y::ACSet;
    monic=false, epic=false, iso=false, random=false, predicates=(;),
    type_components=(;), initial=(;), error_failures=false, no_bind=false)
  S, Sy = acset_schema.([X,Y])
  S == Sy || error("Schemas must match for morphism search")
  Ob = Tuple(objects(S))
  Attr = Tuple(attrtypes(S))
  ObAttr = Tuple(objects(S) ∪ attrtypes(S))

  # Fail early if no monic/isos exist on cardinality grounds.
  if iso isa Bool
    iso = iso ? ObAttr : ()
  end
  if monic isa Bool
    monic = monic ? ObAttr : ()
  end
  if epic isa Bool
    epic = epic ? Ob : ()
  end
  if no_bind isa Bool 
    no_bind = no_bind ? Attr : ()
  end

  iso_failures = Iterators.filter(c->nparts(X,c)!=nparts(Y,c),iso)
  mono_failures = Iterators.filter(c->nparts(X,c)>nparts(Y,c),monic)  
  epi_failures = Iterators.filter(c->nparts(X,c)<nparts(Y,c),epic)  

  if !all(isempty, [iso_failures, mono_failures, epi_failures])
    if !error_failures 
      return false 
    else error("""
      Cardinalities inconsistent with request for...
        iso at object(s) $iso_failures
        mono at object(s) $mono_failures
        epi at object(s) $epi_failures
      """)
    end
  end
  
  # Fail if there are "free floating attribute variables"
  for a_type in attrtypes(S) 
    a_type ∈ (monic ∪ iso ∪ no_bind) && continue # attrvars ↦ attrvars
    attrs′ = attrs(S, just_names=true, to=a_type)
    avars = union(AttrVar[],collect.([filter(x->x isa AttrVar, X[f]) for f in attrs′])...)
    assigned = partial_assignments(get(initial, a_type, []); is_attr=true)
    assigned′ = first.(collect(assigned))
    unassigned = setdiff(parts(X, a_type), [v.val for v in avars] ∪ assigned′)
    if !isempty(unassigned)
      error("Cannot search for morphisms with free-floating variables: $unassigned")
    end
  end
  

  # Injections between finite sets of the same size are bijections, so reduce to that case.
  monic = unique([iso..., monic...])

  if error_failures 
    uns = naturality_failures(X,Y,initial,type_components)
    all(isempty,[uns[a] for a in keys(uns)]) ||
      error(sprint(show_naturality_failures, uns))
  end

  pred_nt = NamedTuple{Ob}(let dic = get(predicates, c, Dict()); 
    Union{Set{Int}, Nothing}[haskey(dic, p) ? Set(dic[p]) : nothing for p in 1:maxpart(X,c)] 
  end for c in Ob)

  # Initialize state variables for search.
  assignment = merge(
    NamedTuple{Ob}(zeros(Int, maxpart(X, c)) for c in Ob),
    NamedTuple{Attr}(Pair{Int,Union{AttrVar,attrtype_type(X,c)}}[
      0 => AttrVar(0) for _ in 1:maxpart(X,c)] for c in Attr)
  )
  assignment_depth = map(copy, assignment)
  inv_assignment = NamedTuple{ObAttr}(
    (c in monic ? zeros(Int, maxpart(Y, c)) : nothing) for c in ObAttr)
  loosefuns = NamedTuple{Attr}(
    isnothing(type_components) ? identity : get(type_components, c, identity) for c in Attr)

  images = NamedTuple{Ob}(
    (c in epic ? zeros(Int, nparts(Y, c)) : nothing) for c in Ob)
  unassigned = NamedTuple{Ob}(
    (c in epic ? [nparts(X, c)] : nothing) for c in Ob)

  state = BacktrackingState(assignment, assignment_depth, 
                            inv_assignment, X, Y, loosefuns, pred_nt,
                            images, unassigned)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments; is_attr = c ∈ Attr)
      if c ∈ ob(S)
        assign_elem!(state, 0, c, x, y) || return false
      else 
        # assign_elem! doesn't expect an attrtype part
        state.assignment[c][x][1] == 0 || assignment[c][x][2] == y || return false
        state.assignment[c][x] = 1 => y
      end 
    end
  end
  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1; random=random)
end

"""
Note: a successful search returns an *iterator* of solutions, rather than 
a single solution. See `postprocess_search_results`.
"""
function backtracking_search(f, state::BacktrackingState, depth::Int; 
                              random=false) 
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    if any(!=(identity), state.type_components)
      return f([LooseACSetTransformation(
        state.assignment, state.type_components, state.dom, state.codom)])
    else
      m = Dict(k=>!isnothing(v) for (k,v) in pairs(state.inv_assignment))
      return f(postprocess_search_results(state.dom, state.codom, state.assignment, m))
    end
  elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return false
  end
  c, x = mrv_elem

  # Attempt all assignments of the chosen element.
  Y = state.codom
  for y in (random ? shuffle : identity)(parts(Y, c))
    (assign_elem!(state, depth, c, x, y) 
      && backtracking_search(f, state, depth + 1)) && return true
    unassign_elem!(state, depth, c, x)
  end
  return false
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState, depth)
  S = acset_schema(state.dom)
  mrv, mrv_elem = Inf, nothing
  Y = state.codom
  for c in ob(S), x in parts(state.dom, c)
    state.assignment[c][x] == 0 || continue
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
assign_elem!(state::BacktrackingState{<:StructACSet{S}}, depth, c, x, y) where S = 
  _assign_elem!(Val{S}, state, depth,Val{c},x,y)
assign_elem!(state::BacktrackingState{<:DynamicACSet}, depth, c, x, y) =
  runtime(_assign_elem!,acset_schema(state.dom), state, depth,c,x,y)


@ct_enable function _assign_elem!(@ct(S), state::BacktrackingState, depth, @ct(c), x, y)
  y′ = state.assignment[@ct c][x]
  y′ == y && return true  # If x is already assigned to y, return immediately.
  y′ == 0 || return false # Otherwise, x must be unassigned.
  if !isnothing(state.inv_assignment[@ct c]) && state.inv_assignment[@ct c][y] != 0
    # Also, y must unassigned in the inverse assignment.
    return false
  end

  # With an epic constraint, fail based on the # of unassigned in dom vs codom
  if (!isnothing(state.image[@ct c]) && state.image[@ct c][y]!=0
      && only(state.unassigned[@ct c]) <= count(==(0), state.image[@ct c]))
    return false
  end


  isnothing(state.predicates[c][x]) || y ∈ state.predicates[c][x] || return false

  # Check attributes first to fail as quickly as possible.
  X, Y = state.dom, state.codom
  @ct_ctrl for (f, _, d) in attrs(S; from=c)
    dcomp = state.type_components[@ct(d)]
    if subpart(X,x,@ct(f)) isa AttrVar
      xcount, xval = state.assignment[@ct(d)][subpart(X,x,@ct(f)).val]
      if xcount > 0 && dcomp(xval) != subpart(Y,y,@ct(f)) 
         return false
      end
    elseif dcomp(subpart(X,x,@ct f)) != subpart(Y,y,@ct f)
      return false
    end 

  end

  # Make the assignment and recursively assign subparts.
  state.assignment[@ct c][x] = y
  state.assignment_depth[@ct c][x] = depth
  if !isnothing(state.inv_assignment[@ct c])
    state.inv_assignment[@ct c][y] = x
  end
  if !isnothing(state.image[@ct c])
    state.image[@ct c][y] += 1
    state.unassigned[@ct c][1] -= 1
  end

  # Enforce naturality for all attrs, e.g. assigning an edge fixes its weight
  @ct_ctrl for (f, _, d) in attrs(S; from=c)
    if subpart(X, x, @ct(f)) isa AttrVar 
      v = subpart(X, x, @ct(f)).val
      xcount, _ = state.assignment[@ct d][v]
      Yf = subpart(Y, y, @ct(f))
      invD = state.inv_assignment[@ct d]
      state.assignment[@ct d][v] = xcount+1 => Yf
      if !isnothing(invD)
        (Yf isa AttrVar && invD[Yf.val] ∈ [0, v]) || return false
        invD[Yf.val] = v 
      end
    end
  end

  @ct_ctrl for (f, _, d) in homs(S; from=c) 
    assign_elem!(state, depth, @ct(d), subpart(X, x, @ct f),
                 subpart(Y, y, @ct f)) || return false
  end
  return true
end

""" Unassign the element (c,x) in the current assignment.
"""
unassign_elem!(state::BacktrackingState{<:StructACSet{S}}, depth, c, x) where S = 
  _unassign_elem!(Val{S}, state, depth,Val{c},x)
unassign_elem!(state::BacktrackingState{<:DynamicACSet}, depth, c, x) =
  runtime(_unassign_elem!,acset_schema(state.dom), state, depth,c,x)

@ct_enable function _unassign_elem!(@ct(S), state::BacktrackingState, depth, @ct(c), x) 
  state.assignment[@ct c][x] == 0 && return
  assign_depth = state.assignment_depth[@ct c][x]
  @assert assign_depth <= depth
  if assign_depth == depth
    X = state.dom
    if !isnothing(state.inv_assignment[@ct c])
      y = state.assignment[@ct c][x]
      state.inv_assignment[@ct c][y] = 0
    end
    if !isnothing(state.unassigned[@ct c])
      state.unassigned[@ct c][1] += 1
      state.image[@ct c][state.assignment[@ct c][x]] -= 1
    end

    @ct_ctrl for (f,_,d) in attrs(S; from=c)
      if subpart(X,x,@ct(f)) isa AttrVar
        v = subpart(X,x,@ct(f)).val
        n, αv = state.assignment[@ct(d)][v]
        state.assignment[@ct(d)][v]= (n-1 => αv)
        invD = state.inv_assignment[@ct d]
        # Reset inv assignment if it's we're unsetting last reference
        if n == 1 && αv isa AttrVar && !isnothing(invD) && invD[αv.val] == v
          invD[αv.val] = 0
        end
      end
    end

    state.assignment[@ct c][x] = 0
    state.assignment_depth[@ct c][x] = 0
    @ct_ctrl for (f, _, d) in homs(S; from=c)
      unassign_elem!(state, depth, @ct(d), subpart(X,x,@ct(f)))
    end
  end
end

""" 
A hom search result might not have all the data for an ACSetTransformation
explicitly specified. For example, if there is a cartesian product of possible
assignments which could not possibly constrain each other, then we should
iterate through this product at the very end rather than having the backtracking
search navigate the product space. Currently, this is only done with assignments
for floating attribute variables, but in principle this could be applied in the
future to, e.g., free-floating vertices of a graph or other coproducts of 
representables.

This function takes a result assignment from backtracking search and returns an
iterator of the implicit set of homomorphisms that it specifies.
"""
function postprocess_search_results(dom, codom, assgn, monic)
  S = acset_schema(dom)
  od = Dict{Symbol,Vector{Int}}(k=>(assgn[k]) for k in objects(S))

  # Compute possible assignments for all free variables
  free_data = map(attrtypes(S)) do k
    assigned = [v.val for (_, v) in assgn[k] if v isa AttrVar]
    valid_targets = setdiff(parts(codom, k), monic[k] ? assigned : [])
    free_vars = findall(==(AttrVar(0)), last.(assgn[k]))
    N = length(free_vars)
    prod_iter = Iterators.product(fill(valid_targets, N)...)
    if monic[k]
      prod_iter = Iterators.filter(x->length(x)==length(unique(x)), prod_iter)
    end
    (free_vars, prod_iter) # prod_iter = valid assignments for this attrtype
  end
  
  # Homomorphism for each element in the product of the prod_iters
  return Iterators.map(Iterators.product(last.(free_data)...) ) do combo 
    ad = Dict(map(zip(attrtypes(S), first.(free_data), combo)) do (k, xs, vs)
      vec = last.(assgn[k])
      vec[xs] = AttrVar.(collect(vs))
      k => vec
    end)
    comps = merge(NamedTuple(od),NamedTuple(ad))
    ACSetTransformation(comps, dom, codom)
  end
end

# Macros 
########


"""
Provides a shorthand for constructing a tight acset transformation by giving its
components. Homomorphism search allows partial specification, with the return
value being the unique extension if it exists.

Keyword arguments can be passed on to the search function after the body of the
transformation.

Example usage for transformation between `WeightedGraph{String}`:

```
@acset_transformation A B begin
  V = [3,5,2] #complete specification can be a vector
  E = Dict(1 => 3, 4 => 3) #otherwise use a dict
end monic=true iso=[:V] or [:V,:E], etc
```
"""
macro acset_transformation(dom,cod,kw...)
  kw = map(parse_kwargs,kw)
  Expr(:call,esc(:homomorphism),esc(dom),esc(cod), Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformation(dom,cod,body,kw...)
  kw = map(parse_kwargs,kw)
  initial = process_initial(body)
  Expr(:call,esc(:homomorphism),esc(dom),esc(cod),initial,Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformations(dom,cod,kw...)
  kw = map(parse_kwargs,kw)
  Expr(:call,esc(:homomorphisms),esc(dom),esc(cod),Expr(:kw,:error_failures,true),kw...)
end
macro acset_transformations(dom,cod,body,kw...)
  kw = map(parse_kwargs,kw)
  initial = process_initial(body)
  Expr(:call,esc(:homomorphisms),esc(dom),esc(cod),initial,Expr(:kw,:error_failures,true),kw...)
end
function process_initial(expr)
  initial = @match expr begin
    Expr(:block,lines...) => filter(!isnothing,map(escape_assignment_lhs,lines))
    Expr(:(=),x,y) => parse_kwargs(expr) #does this ever happen?
    _ => error("Expected begin...end block or kwarg, received $expr")
  end
  isa(initial,Vector) ? length(initial) > 0 ?
      Expr(:kw,:initial,Expr(:tuple,initial...)) :
      Expr(:kw,:initial,Expr(:tuple,Expr(:parameters,))) :
    initial
end
function parse_kwargs(expr)
  @match expr begin
    Expr(:(=),x,y) => Expr(:kw,x,y)
    _ => nothing
  end
end
function escape_assignment_lhs(expr)
  @match expr begin
    Expr(:(=),x,y) => Expr(:(=),esc(x),y)
    _ => nothing
  end
end
