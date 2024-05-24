"""
Functionality related to search problems involving ACSets, e.g.:

- enumerating Hom(X,Y) where X,Y are ACSets
- enumerating subobjects of an ACSet, X
- enumerating partial overlaps between ACSets
"""
module HomSearch 
export ACSetHomomorphismAlgorithm, BacktrackingSearch, HomomorphismQuery,
       VMSearch,homomorphism, homomorphisms, is_homomorphic,
       isomorphism, isomorphisms, is_isomorphic,
       @acset_transformation, @acset_transformations,
       subobject_graph, partial_overlaps, maximum_common_subobject,
       compile_hom_search
   
using ...Theories, ..CSets, ..FinSets, ..FreeDiagrams, ..Subobjects
using ...Graphs.BasicGraphs
using ..CSets: map_components
using ACSets.DenseACSets: attrtype_type, delete_subobj!

using Random, StructEquality
using CompTime
using MLStyle: @match, @data
using DataStructures: BinaryHeap, DefaultDict

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
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`. Use 
the keyword argument `type_components` to specify nontrivial components on 
attribute types for a loose homomorphism. These components must be callable:
either Julia functions on the appropriate types or FinFunction(Dict(...)).

Use the keyword argument `alg` to set the homomorphism-finding algorithm. By
default, a backtracking search algorithm is used ([`BacktrackingSearch`](@ref)).
Use the keyword argument error_failures = true to get errors explaining 
any immediate inconsistencies in specified initial data.

The keyword `predicates` accepts a Dict{Ob, Dict{Int, Union{Nothing, AbstractVector{Int}}}}
For each part of the domain, we have the option to give a constraint as a
boolean function of the current assignment and tentative value to assign. E.g.
`predicates = (E = Dict(2 => [2,4,6]))` would only find matches
which assigned edge#2 to edge #2, #4, or #6 in the codomain.

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

function homomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) 
  results = []
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
    type_components=(;), initial=(;), error_failures=false)
  S, Sy = acset_schema.([X,Y])
  S == Sy || error("Schemas must match for morphism search")
  Ob = Tuple(objects(S))
  Attr = Tuple(attrtypes(S))
  ObAttr = Tuple(objects(S) ∪ attrtypes(S))
  # Fail if there are "free floating attribute variables"
  all(attrtypes(S)) do a_type
    ats = attrs(S, just_names=true, to=a_type)
    avs = collect.([filter(x->x isa AttrVar, X[f]) for f in ats])
    pa = partial_assignments(get(initial, a_type, []); is_attr=true)
    initkeys = AttrVar.(keys(collect(pa)))
    length(unique(vcat(initkeys, avs...))) == nparts(X, a_type) 
  end || error("Cannot search for morphisms with free-floating variables")

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
  iso_failures = Iterators.filter(c->nparts(X,c)!=nparts(Y,c),iso)
  mono_failures = Iterators.filter(c->nparts(X,c)>nparts(Y,c),monic)  
  epi_failures = Iterators.filter(c->nparts(X,c)<nparts(Y,c),epic)  

  if !all(isempty, [iso_failures,mono_failures,epi_failures])
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

function backtracking_search(f, state::BacktrackingState, depth::Int; 
                              random=false) 
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    if any(!=(identity), state.type_components)
      return f(LooseACSetTransformation(
        state.assignment, state.type_components, state.dom, state.codom))
    else
      S = acset_schema(state.dom)
      od = Dict{Symbol,Vector{Int}}(k=>(state.assignment[k]) for k in objects(S))
      ad = Dict(k=>last.(state.assignment[k]) for k in attrtypes(S))
      comps = merge(NamedTuple(od),NamedTuple(ad))
      return f(ACSetTransformation(comps, state.dom, state.codom))
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

  @ct_ctrl for (f,_,d) in attrs(S; from=c)
    if subpart(X,x,@ct(f)) isa AttrVar
      v = subpart(X,x,@ct(f)).val
      xcount,_ = state.assignment[@ct d][v]
      state.assignment[@ct d][v] = xcount+1 => subpart(Y,y,@ct(f))
    end
  end

  @ct_ctrl for (f, _, d) in homs(S; from=c) 
    assign_elem!(state, depth, @ct(d), subpart(X,x,@ct f),subpart(Y,y,@ct f)) || return false
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
      end
    end

    state.assignment[@ct c][x] = 0
    state.assignment_depth[@ct c][x] = 0
    @ct_ctrl for (f, _, d) in homs(S; from=c)
      unassign_elem!(state, depth, @ct(d), subpart(X,x,@ct(f)))
    end
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

# VM Search
#----------


""" Find attributed ``C``-set homomorphisms using a virtual machine.
This algorithm compiles the backtracking search algorithm into a flat sequence 
of instructions for faster execution.
"""

struct VMSearch <: ACSetHomomorphismAlgorithm end

function homomorphisms(X::ACSet, Y::ACSet, ::VMSearch; prog=nothing)
  prog = isnothing(prog) ? compile_hom_search(X) : prog
  find_all(prog, X, Y)
end

struct Reg
  idx::Int
end

Base.show(io::IO, r::Reg) = print(io, "[$(r.idx)]")

@data SearchInst begin
  # Iterate through all the rows of a table

  Loop(x::Symbol, reg::Reg)

  # Load a subpart into memory
  Load(from::Reg, subpart::Symbol, into::Reg)

  # Compare two registers for equality, backtrack if they aren't equal
  Compare(r1::Reg, r2::Reg)
end

Base.show(io::IO, l::Loop) = print(io, "LOOP $(l.x)#$(l.reg)")
Base.show(io::IO, l::Load) = print(io, "LOAD $(l.subpart): $(l.from)->$(l.into)")
Base.show(io::IO, l::Compare) = print(io, "COMPARE $(l.r1) ? $(l.r2)")

struct Machine
  registers::Vector{Int}
end

Base.getindex(m::Machine, r::Reg) = m.registers[r.idx]
Base.setindex!(m::Machine, i::Int, r::Reg) = (m.registers[r.idx] = i)

@struct_hash_equal struct NamedPart
  ob::Symbol
  idx::Int
end

struct Program
  next_reg::Ref{Int}
  instructions::Vector{SearchInst}
  lookup::Dict{NamedPart, Reg}
end

function Base.show(io::IO, p::Program)
  for (i, ins) in enumerate(p.instructions)
    print(io, "$i: ")
    println(io, ins)
  end
end

function interpret_search!(m::Machine, prog::Program, a::ACSet, pc::Int, cb::Function)
  if pc > length(prog.instructions)
    cb(m.registers)
  else
    @match prog.instructions[pc] begin
      Loop(x, reg) =>
        for i in parts(a, x)
          m[reg] = i
          interpret_search!(m, prog, a, pc+1, cb)
        end
      Load(from, f, into) => begin
        m[into] = subpart(a, m[from], f)
        interpret_search!(m, prog, a, pc+1, cb)
      end
      Compare(r1, r2) =>
        if m[r1] == m[r2]
          interpret_search!(m, prog, a, pc+1, cb)
        end
    end
  end
end

function find_all(prog::Program, from::ACSet, to::ACSet)
  schema = acset_schema(from)
  homs = NamedTuple{tuple(objects(schema)...), Tuple{[Vector{Int} for _ in objects(schema)]...}}[]
  cb = push_callback(from, homs, prog)
  interpret_search!(Machine(zeros(Int, prog.next_reg[])), prog, to, 1, cb)
  homs
end

function nextreg!(p::Program)
  r = Reg(p.next_reg[])
  p.next_reg[] += 1
  r
end

"""
ordering strategies: 
 - neighbor - order by # of neighbors
 - connected - order by neighbors but prioritize connected components
 - random
"""
function compile_hom_search(X::ACSet, order=nothing; strat=:neighbor)
  S = acset_schema(X)
  if isnothing(order)
    order, queue, seen = Tuple{Symbol,Int}[], Int[], Set{Int}()
    all_parts = vcat([[(o,p) for p in parts(X,o)] for o in ob(S)]...)
    all_d = Dict(p=>i for (i,p) in enumerate(all_parts))
    neighbors = map(all_parts) do (o,p)
      ns = Int[] # indices of neighboring parts
      for (f, _, b) in homs(S; from=o)
        push!(ns, all_d[(b, X[p,f])])
      end
      for (f, a, _) in homs(S; to=o)
        if a != o 
          for ip in incident(X, p, f)
            push!(ns, all_d[(a, ip)])
          end
        end
      end
      ns
    end
    # order neighbor vectors by which ones have the most neighbors
    ordered_neighbors = [sort(ns; by=i->length(neighbors[i])) for ns in neighbors]
    # order parts by same metric
    n_ord = sort(1:length(all_parts), by=i->length(neighbors[i]))
    if strat == :neighbor
      order = all_parts[n_ord] |> reverse
    elseif strat == :random 
      order = shuffle(all_parts)
    elseif strat == :connected
      while !(isempty(n_ord) && isempty(queue))
        if isempty(queue)
          nxt = pop!(n_ord)
          if nxt ∉ seen 
            queue = [nxt]
          end
        else
          curr = pop!(queue)
          push!(order, all_parts[curr]); push!(seen, curr)
          append!(queue, filter(i-> i ∉ seen && i ∉ queue, ordered_neighbors[curr]))
        end
      end
    else 
      error("Unknown order strategy: $strat")
    end
  end
  compile_hom_search(X, [NamedPart(ob, i) for (ob, i) in order])
end

function push_callback(a::ACSet, homs::Vector{T}, prog::Program) where {T<:NamedTuple}
  schema = acset_schema(a)
  function cb(regs::Vector{Int})
    hom = T([zeros(Int, nparts(a, ob)) for ob in objects(schema)])
    for (k,v) in prog.lookup
      hom[k.ob][k.idx] = regs[v.idx]
    end
    push!(homs, hom)
  end
end

allparts(a::ACSet) = Set([NamedPart(ob, i) for ob in objects(acset_schema(a)) for i in parts(a, ob)])

function compile_hom_search(a::ACSet, order::Vector{NamedPart})
  @assert allparts(a) == Set(order)
  schema = acset_schema(a)
  prog = Program(Ref(1), SearchInst[], Dict{NamedPart, Reg}())
  # validate 
  for o in ob(schema) 
    parts = [p.idx for p in order if p.ob == o]
    isperm(parts) && length(parts) == nparts(a, o) || error("Bad part $o $parts")
  end
  for p in order
    if p ∈ keys(prog.lookup)
      continue
    end
    p_reg = nextreg!(prog)
    prog.lookup[p] = p_reg
    push!(prog.instructions, Loop(p.ob, p_reg))
    to_process = [p]
    while !isempty(to_process)
      next = pop!(to_process)
      next_reg = prog.lookup[next]
      for (f, _, d) in homs(schema; from=next.ob)
        r = nextreg!(prog)
        push!(prog.instructions, Load(next_reg, f, r))
        q = NamedPart(d, a[next.idx, f])
        if q ∈ keys(prog.lookup)
          push!(prog.instructions, Compare(prog.lookup[q], r))
        else
          prog.lookup[q] = r
          push!(to_process, q)
        end
      end
    end
  end

  prog
end

# Maximum Common C-Set
######################

""" Compute the size of a C-Set

Defintion: let 𝐺: C → 𝐒et be a C-set, we define the _size_ of 𝐺 to be ∑_{c ∈ C}
|𝐺c|.  For example, under this definition, the size of:
  * a graph G is |GE| + |GV| (num edges + num vertices)
  * a Petri net P is |PT| + |PS| + |PI| + |PO| (num transitions + num species +
    num input arcs + num output arcs).
"""
total_parts(X::ACSet) = mapreduce(oₛ -> nparts(X, oₛ), +, objects(acset_schema(X)); init=0)
total_parts(X::ACSetTransformation) = total_parts(dom(X)) 

"""
Enumerate subobjects of an ACSet in order of largest to smallest 
(assumes no wandering variables).
"""
struct SubobjectIterator
  top::ACSet
end

Base.eltype(::Type{SubobjectIterator}) = Subobject
Base.IteratorSize(::Type{SubobjectIterator}) = Base.SizeUnknown()

"""
Preorder of subobjects via inclusion. 
Returns a graph + list of subobjects corresponding to its vertices. 
The subobjects are ordered by decreasing size (so it's topologically sorted)
"""
function subobject_graph(X::ACSet)
  S = acset_schema(X)
  subs = X |> SubobjectIterator |> collect
  G = Graph(length(subs))
  for (i,s1) in enumerate(subs)
    for (j,s2) in enumerate(subs)
      if all(ob(S)) do o 
          collect(hom(s1)[o]) ⊆ collect(hom(s2)[o])
        end
        add_edge!(G, i, j)
      end
    end
  end
  return (G, subs)
end

"""
seen       - any subobject we've seen so far
to_recurse - frontier of subobjects we've yet to recursively explore
to_yield   - Subobjects which we've yet to yield
"""
struct SubobjectIteratorState
  seen::Set{ACSetTransformation}
  to_recurse::BinaryHeap
  to_yield::BinaryHeap
  function SubobjectIteratorState()  
    heap = BinaryHeap(Base.By(total_parts, Base.Order.Reverse), ACSetTransformation[])
    new(Set{ACSetTransformation}(), heap, deepcopy(heap))
  end
end
Base.isempty(S::SubobjectIteratorState) = isempty(S.seen)
function Base.push!(S::SubobjectIteratorState,h::ACSetTransformation)
  push!(S.seen, h); push!(S.to_recurse, h); push!(S.to_yield, h)
end

"""This would be much more efficient with canonical isomorph"""
function is_seen(S::SubobjectIteratorState, f::ACSetTransformation)
  for h in S.seen 
    if any(σ -> force(σ⋅h) == force(f), isomorphisms(dom(f),dom(h)))
      return true 
    end
  end
  return false
end

"""
We recurse only if there is nothing to yield or we have something to recurse on 
that is bigger than the biggest thing in our to-yield set.
"""
should_yield(S::SubobjectIteratorState) = !isempty(S.to_yield) && (
    isempty(S.to_recurse) || total_parts(first(S.to_yield)) > total_parts(first(S.to_recurse)))


function Base.iterate(Sub::SubobjectIterator, state=SubobjectIteratorState())
  S = acset_schema(Sub.top)
  T = id(Sub.top)
  if isempty(state) # first time
    push!(state.seen, T); push!(state.to_recurse, T)
    return (Subobject(T), state)
  end

  # Before recursing, check if we should yield things or terminate
  if should_yield(state)
    return (Subobject(pop!(state.to_yield)), state)
  end
  if isempty(state.to_recurse) 
    return nothing
  end
  # Explore by trying to delete each ACSet part independently 
  X = pop!(state.to_recurse)
  dX = dom(X)
  for o in ob(S)
    for p in parts(dX, o)
      rem = copy(dX)
      comps = Dict{Symbol, Any}(pairs(delete_subobj!(rem, Dict([o => [p]]))))
      rem_free_vars!(rem)
      for at in attrtypes(S)
        comps[at] = map(AttrVar.(parts(rem, at))) do part
          for (f, c, _) in attrs(S; to=at)
            inc = incident(rem, part, f)
            if !isempty(inc)
              return dX[comps[c][first(inc)], f]
            end
          end
        end
      end
      h = ACSetTransformation(rem, dX; comps...) ⋅ X
      if !is_seen(state, h)
        push!(state, h)
      end
    end
  end

  if should_yield(state)
    return (Subobject(pop!(state.to_yield)), state)
  elseif !isempty(state.to_recurse)
    return Base.iterate(Sub, (state))
  else 
    return nothing
  end 
end

struct OverlapIterator
  acsets::Vector{ACSet}
  top::Int
  abstract::Vector{Symbol}
  function OverlapIterator(Xs::Vector{T}; abstract=true) where T<:ACSet
    S = acset_schema(first(Xs))
    abstract_attrs = if abstract isa Bool 
      abstract ? attrtypes(S) : Symbol[]
    else 
      abstract 
    end
    new(Xs, argmin(total_parts.(Xs)), abstract_attrs)
  end
end
Base.eltype(::Type{OverlapIterator}) = Multispan
Base.IteratorSize(::Type{OverlapIterator}) = Base.SizeUnknown()

mutable struct OverlapIteratorState
  curr_subobj::Union{Nothing,ACSetTransformation}
  subobject_state::Iterators.Stateful{SubobjectIterator}
  seen::Set{Multispan}
  maps::Union{Nothing,Iterators.Stateful{<:Iterators.ProductIterator}}
  OverlapIteratorState(x::ACSet) = 
    new(nothing, Iterators.Stateful(SubobjectIterator(x)), Set{Multispan}(), nothing)
end

# Could be cleaner/faster if we used CSetAutomorphisms to handle symmetries
"""
Given a list of ACSets X₁...Xₙ, find all multispans A ⇉ X ordered by decreasing 
number of total parts of A.

We search for overlaps guided by iterating through the subobjects of the 
smallest ACSet.
  
If a subobject of the first object, A↪X, has multiple maps into X₁, then 
we need to cache a lot of work because we consider each such subobject 
independently. This is the maps from A into all the other objects as well as the 
automorphisms of A.  
"""
function Base.iterate(Sub::OverlapIterator, state=nothing)
  state = isnothing(state) ? OverlapIteratorState(Sub.acsets[Sub.top]) : state
  # if we are not computing overlaps from a particular subobj, 
  if isnothing(state.curr_subobj) # pick the next subobj
    isnothing(state.maps) || error("Inconsistent overlapiterator state")
    if isempty(state.subobject_state)
      return nothing
    else 
      state.curr_subobj = hom(popfirst!(state.subobject_state))
      return Base.iterate(Sub, state)
    end
  elseif isnothing(state.maps) # compute all the maps out of curr subobj
    subobj = state.curr_subobj
    abs_subobj = abstract_attributes(dom(subobj), Sub.abstract) ⋅ subobj
    Y = dom(abs_subobj)
    # don't repeat work if already computed syms/maps for something iso to Y
    for res in state.seen
      σ = isomorphism(Y, apex(res))
      if !isnothing(σ)
        state.subobj = nothing
        return (Multispan(map(m->σ⋅m, res)), state)
      end
    end
    # Compute the automorphisms so that we can remove spurious symmetries
    syms = isomorphisms(Y, Y)
    # Get monic maps from Y into each of the objects. The first comes for free
    maps = Vector{ACSetTransformation}[]
    for (i, X) in enumerate(Sub.acsets)
      if i == Sub.top 
        push!(maps, [abs_subobj])
      else 
        fs = homomorphisms(Y, X; monic=ob(acset_schema(Y)))
        real_fs = Set() # quotient fs via automorphisms of Y
        for f in fs 
          if all(rf->all(σ -> force(σ⋅f) != force(rf),  syms), real_fs)  
            push!(real_fs, f)
          end
        end
        if isempty(real_fs)
          break # this subobject of Xs[1] does not have common overlap w/ all Xs
        else
          push!(maps, collect(real_fs))
        end
      end
    end
    if length(maps) == length(Sub.acsets)
      state.maps = Iterators.Stateful(Iterators.product(maps...))
    else 
      state.curr_subobj = nothing
    end
    return Base.iterate(Sub, state)
  elseif isempty(state.maps)
    state.maps = nothing; state.curr_subobj = nothing
    return Base.iterate(Sub, state)
  else 
    return (Multispan(collect(popfirst!(state.maps))), state)
  end
end

partial_overlaps(Xs::Vector{T}; abstract=true) where T<:ACSet = OverlapIterator(Xs; abstract)
partial_overlaps(Xs::ACSet...; abstract=true) = partial_overlaps(collect(Xs); abstract)

""" Compute the Maximimum Common C-Sets from a vector of C-Sets.

Find an ACSet ```a`` with maximum possible size (``|a|``) such that there is a  
monic span of ACSets ``a₁ ← a → a₂``. There may be many maps from this overlap 
into each of the inputs, so a Vector{Vector{ACSetTransformations}} per overlap 
is returned (a cartesian product can be taken of these to obtain all possible 
multispans for that overlap). If there are multiple overlaps of equal size, 
these are all returned.

If there are attributes, we ignore these and use variables in the apex of the 
overlap.
"""
function maximum_common_subobject(Xs::Vector{T}; abstract=true) where T <: ACSet
  it = partial_overlaps(Xs; abstract)
  osize = -1
  res = DefaultDict(()->[])
  for overlap in it 
    apx = apex(overlap)
    size = total_parts(apx)
    osize = osize == -1 ? size : osize
    if size < osize return res end 
    push!(res[apx], overlap)
  end 
  return res
end

maximum_common_subobject(Xs::T...; abstract=true) where T <: ACSet = 
  maximum_common_subobject(collect(Xs); abstract)


end # module
