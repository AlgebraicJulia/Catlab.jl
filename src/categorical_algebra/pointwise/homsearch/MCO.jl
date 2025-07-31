module MCO

export subobject_graph, partial_overlaps, maximum_common_subobject

using DataStructures: DefaultDict, BinaryHeap

using ACSets
using ACSets.DenseACSets: delete_subobj!

using .....Graphs, ....Cats
using ...Pointwise

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
  cat::ACSetCategory
  function SubobjectIterator(top::ACSet, cat=nothing)
    cat = isnothing(cat) ? infer_acset_cat(top) : cat
    new(top, cat)
  end
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
function is_seen(cat, S::SubobjectIteratorState, f::ACSetTransformation)
  for h in S.seen
    for σ in isomorphisms(dom(f),dom(h); cat) 
      σ = force(σ; cat) # TODO this should be done automatically in homsearch 
      force(compose[cat](σ,h); cat) == force(f; cat) && return true
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
  T = id[Sub.cat](Sub.top)
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
      h = compose[Sub.cat](ACSetTransformation(rem, dX; comps...), X)
      is_seen(Sub.cat, state, h) || push!(state, h)
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
  cat::ACSetCategory
  function OverlapIterator(Xs::Vector{T}; abstract=true, cat=nothing) where T<:ACSet
    S = acset_schema(first(Xs))
    cat = isnothing(cat) ? infer_acset_cat(first(Xs)) : cat
    abstract_attrs = if abstract isa Bool 
      abstract ? attrtypes(S) : Symbol[]
    else 
      abstract 
    end
    new(Xs, argmin(total_parts.(Xs)), abstract_attrs, cat)
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
    abs_subobj = compose[Sub.cat](abstract_attributes(dom(subobj), Sub.abstract), subobj)
    Y = dom(abs_subobj)
    # don't repeat work if already computed syms/maps for something iso to Y
    for res in state.seen
      σ = isomorphism(Y, apex(res))
      if !isnothing(σ)
        state.subobj = nothing
        return (Multispan(map(m->compose[Sub.cat](σ,m), res)), state)
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
          if all(rf->all(σ -> force(compose[Sub.cat](σ,f)) != force(rf),  syms), real_fs)  
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

partial_overlaps(Xs::Vector{T}; abstract=true, kw...) where T<:ACSet = 
  OverlapIterator(Xs; abstract, kw...)

partial_overlaps(Xs::ACSet...; abstract=true, kw...) = 
  partial_overlaps(collect(Xs); abstract, kw...)

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
function maximum_common_subobject(Xs::Vector{T}; abstract=true, kw...) where T <: ACSet
  it = partial_overlaps(Xs; abstract, kw...)
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

maximum_common_subobject(Xs::ACSet...; abstract=true, kw...) = 
  maximum_common_subobject(collect(Xs); abstract, kw...)

end # module