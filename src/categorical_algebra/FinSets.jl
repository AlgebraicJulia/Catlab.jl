""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinFunction, FinDomFunction, force,
  IndexedFinFunction, IndexedFinDomFunction, is_indexed, preimage,
  JoinAlgorithm, NestedLoopJoin, SortMergeJoin

using Compat: isnothing, only

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root!
using FunctionWrappers: FunctionWrapper
using StaticArrays

using ...Theories, ..FreeDiagrams, ..Limits, ..Sets
import ...Theories: dom, codom
using ...CSetDataStructures: insertsorted!, set_data_index!
import ..Limits: limit, colimit, universal
using ..Sets: SetFunctionCallable, SetFunctionIdentity

# Data types
############

# Finite sets
#------------

""" Finite set.

This generic type encompasses the category **FinSet** of finite sets and
functions, through types `FinSet{S} where S <: AbstractSet`, as well as the
skeleton of this category, through the type `FinSet{Int}`. In the latter case,
the object `FinSet(n)` represents the set ``{1,...,n}``.
"""
@auto_hash_equals struct FinSet{S,T} <: SetOb{T}
  set::S
end

FinSet(n::Int) = FinSet{Int,Int}(n)
FinSet(set::S) where {T,S<:AbstractSet{T}} = FinSet{S,T}(set)
FinSet(s::FinSet) = s

Base.iterate(s::FinSet, args...) = iterate(iterable(s), args...)
Base.length(s::FinSet) = length(iterable(s))
Base.in(s::FinSet, elem) = in(s, iterable(s))
iterable(s::FinSet{Int}) = 1:s.set
iterable(s::FinSet{<:AbstractSet}) = s.set

Base.show(io::IO, s::FinSet) = print(io, "FinSet($(s.set))")

# Finite functions
#-----------------

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the vector
representation, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented
by the vector [1,3,2,3].

This type is mildly generalized by [`FinDomFunction`](@ref).
"""
const FinFunction{S, S′, Dom <: FinSet{S}, Codom <: FinSet{S′}} =
  SetFunction{Dom,Codom}

FinFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), FinSet(codom))
FinFunction(f::AbstractVector{Int}) =
  FinDomFunctionVector(f, FinSet(isempty(f) ? 0 : maximum(f)))
FinFunction(f::AbstractVector{Int}, args...) =
  FinDomFunctionVector(f, (FinSet(arg) for arg in args)...)
FinFunction(::typeof(identity), args...) =
  SetFunctionIdentity((FinSet(arg) for arg in args)...)

Sets.show_type(io::IO, ::Type{<:FinFunction}) = print(io, "FinFunction")

""" Function out of a finite set.

This class of functions is convenient because it is exactly the class that can
be represented explicitly by a vector of values from the codomain.
"""
const FinDomFunction{S, Dom<:FinSet{S}, Codom} = SetFunction{Dom,Codom}

FinDomFunction(f::Function, dom, codom) =
  SetFunctionCallable(f, FinSet(dom), codom)
FinDomFunction(f::AbstractVector, args...) = FinDomFunctionVector(f, args...)
FinDomFunction(::typeof(identity), args...) =
  SetFunctionIdentity((FinSet(arg) for arg in args)...)

Sets.show_type(io::IO, ::Type{<:FinDomFunction}) = print(io, "FinDomFunction")

""" Function in **Set** represented by a vector.

The domain of this function is always of type `FinSet{Int}`, with elements of
the form ``{1,...,n}``.
"""
@auto_hash_equals struct FinDomFunctionVector{T,V<:AbstractVector{T},
    Codom<:SetOb{T}} <: FinDomFunction{Int,FinSet{Int,Int},Codom}
  func::V
  codom::Codom
end

FinDomFunctionVector(f::AbstractVector{T}) where T =
  FinDomFunctionVector(f, TypeSet{T}())

function FinDomFunctionVector(f::AbstractVector, dom::FinSet{Int}, codom)
  length(f) == length(dom) ||
    error("Length of vector $f does not match domain $dom")
  FinDomFunctionVector(f, codom)
end

dom(f::FinDomFunctionVector) = FinSet(length(f.func))

(f::FinDomFunctionVector)(x) = f.func[x]

function Base.show(io::IO, f::FinDomFunctionVector)
  print(io, "FinDomFunction($(f.func), $(dom(f)), $(codom(f)))")
end

""" Force evaluation of lazy function or relation.
"""
force(f::FinDomFunction{Int}) = FinDomFunctionVector(map(f, dom(f)), codom(f))
force(f::FinDomFunctionVector) = f

Base.collect(f::SetFunction) = force(f).func

""" Function in **FinSet** represented explicitly by a vector.
"""
const FinFunctionVector{S,T,V<:AbstractVector{T}} =
  FinDomFunctionVector{T,V,FinSet{S,T}}

function Base.show(io::IO, f::FinFunctionVector)
  print(io, "FinFunction($(f.func), $(length(dom(f))), $(length(codom(f))))")
end

Sets.compose_impl(f::FinFunctionVector, g::FinDomFunctionVector) =
  FinDomFunctionVector(g.func[f.func], codom(g))

# Indexed functions
#------------------

""" Indexed function out of a finite set of type `FinSet{Int}`.

Works in the same way as the special case of [`IndexedFinFunction`](@ref),
except that the index is typically a dictionary, not a vector.
"""
struct IndexedFinDomFunction{T,V<:AbstractVector{T},Index,Codom<:SetOb{T}} <:
    SetFunction{FinSet{Int,Int},Codom}
  func::V
  index::Index
  codom::Codom
end

IndexedFinDomFunction(f::AbstractVector{T}; kw...) where T =
  IndexedFinDomFunction(f, TypeSet{T}(); kw...)

function IndexedFinDomFunction(f::AbstractVector{T}, codom::SetOb{T};
                               index=nothing) where T
  if isnothing(index)
    index = Dict{T,Vector{Int}}()
    for (i, x) in enumerate(f)
      set_data_index!(index, x, i)
    end
  end
  IndexedFinDomFunction(f, index, codom)
end

dom(f::IndexedFinDomFunction) = FinSet(length(f.func))
force(f::IndexedFinDomFunction) = f

(f::IndexedFinDomFunction)(x) = f.func[x]

""" Whether the given function is indexed, i.e., supports preimages.
"""
is_indexed(f::IndexedFinDomFunction) = true
is_indexed(f::SetFunction) = false
is_indexed(f::SetFunctionIdentity) = true

""" The preimage (inverse image) of the value y in the codomain.
"""
preimage(f::IndexedFinDomFunction, y) = get_preimage_index(f.index, y)
preimage(f::SetFunctionIdentity, y) = SVector(y)

@inline get_preimage_index(index::AbstractDict, y) = get(index, y, 1:0)
@inline get_preimage_index(index::AbstractVector, y) = index[y]

""" Indexed function between finite sets of type `FinSet{Int}`.

Indexed functions store both the forward map ``f: X → Y``, as a vector of
integers, and the backward map ``f: Y → X⁻¹``, as a vector of sorted vectors of
integers, accessible through the [`preimage`](@ref) function. The backward map
is called the *index*. If it is not supplied through the keyword argument
`index`, it is computed when the object is constructed.

This type is mildly generalized by [`IndexedFinDomFunction`](@ref).
"""
const IndexedFinFunction{V,Index} =
  IndexedFinDomFunction{Int,V,Index,FinSet{Int,Int}}

IndexedFinFunction(f::AbstractVector{Int}, codom; kw...) =
  IndexedFinFunction(f; codom=codom, kw...)

function IndexedFinFunction(f::AbstractVector{Int}; codom=nothing, index=nothing)
  if isnothing(codom) && isnothing(index)
    codom = isempty(f) ? 0 : maximum(f)
  elseif isnothing(codom)
    codom = length(index)
  end
  codom = FinSet(codom)
  if isnothing(index)
    index = [ Int[] for j in codom ]
    for (i, j) in enumerate(f)
      insertsorted!(index[j], i)
    end
  else
    length(index) == length(codom) ||
      error("Index length $(length(index)) does not match codomain $codom")
  end
  IndexedFinDomFunction(f, index, codom)
end

# For now, we do not preserve or compose indices, only the function vectors.
Sets.compose_impl(f::Union{FinFunctionVector,IndexedFinFunction},
                  g::Union{FinDomFunctionVector,IndexedFinDomFunction}) =
  FinDomFunctionVector(g.func[f.func], codom(g))

# Limits
########

function limit(Xs::EmptyDiagram{<:FinSet{Int}})
  Limit(Xs, SMultispan{0}(FinSet(1)))
end

function universal(lim::Terminal{<:FinSet{Int}},
                   cone::SMultispan{0,<:FinSet{Int}})
  FinFunction(ones(Int, length(apex(cone))))
end

function limit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::BinaryProduct{<:FinSet{Int}}, cone::Span{<:FinSet{Int}})
  f, g = cone
  m, n = length.(codom.(cone))
  indices = LinearIndices((m, n))
  FinFunction(i -> indices[f(i),g(i)], apex(cone), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = [FinFunction(i -> indices[i][j], n, ns[j]) for j in 1:length(ns)]
  Limit(Xs, Multispan(FinSet(n), πs))
end

function universal(lim::Product{<:FinSet{Int}}, cone::Multispan{<:FinSet})
  ns = length.(codom.(cone))
  indices = LinearIndices(Tuple(ns))
  FinFunction(i -> indices[(f(i) for f in cone)...], apex(cone), ob(lim))
end

function limit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m = length(dom(pair))
  eq = FinFunction(filter(i -> f(i) == g(i), 1:m), m)
  Limit(pair, SMultispan{1}(eq))
end

function limit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(para, SMultispan{1}(eq))
end

function universal(lim::Equalizer{<:FinSet{Int}},
                   cone::SMultispan{1,<:FinSet{Int}})
  ι = collect(incl(lim))
  h = only(cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end

""" Algorithm for limit of spans or multispans out of finite sets.

In the context of relational databases, such limits are joins.
"""
abstract type JoinAlgorithm <: LimitAlgorithm end

""" [Nested-loop join](https://en.wikipedia.org/wiki/Nested_loop_join) algorithm.

This is the naive algorithm for computing joins.
"""
struct NestedLoopJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}};
               alg::LimitAlgorithm=NestedLoopJoin())
  limit(cospan, alg)
end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}}, ::NestedLoopJoin)
  # A nested-loop join is exactly what you get by composing the above algorithms
  # for products and equalizers, except that we handle the "nested" loops using
  # `CartesianIndices`.
  limit(cospan, ComposeProductEqualizer())
end

""" [Sort-merge join](https://en.wikipedia.org/wiki/Sort-merge_join) algorithm.
"""
struct SortMergeJoin <: JoinAlgorithm end

function limit(cospan::Multicospan{<:SetOb,<:FinDomFunction{Int}}, ::SortMergeJoin)
  funcs = map(collect, legs(cospan))
  sorts = map(sortperm, funcs)
  values = similar_mutable(funcs, eltype(apex(cospan)))
  ranges = similar_mutable(funcs, UnitRange{Int})

  function next_range!(i::Int)
    f, sort = funcs[i], sorts[i]
    n = length(f)
    start = last(ranges[i]) + 1
    ranges[i] = if start <= n
      val = values[i] = f[sort[start]]
      stop = start + 1
      while stop <= n && f[sort[stop]] == val; stop += 1 end
      start:(stop - 1)
    else
      start:n
    end
  end

  πs = map(_ -> Int[], funcs)
  for i in eachindex(ranges)
    ranges[i] = 0:0
    next_range!(i)
  end
  while !any(isempty, ranges)
    if all(==(values[1]), values)
      # TODO: Make more efficient by preallocating larger arrays.
      for index in CartesianIndices(Tuple(ranges))
        for i in eachindex(πs)
          push!(πs[i], sorts[i][index[i]])
        end
      end
      for i in eachindex(ranges)
        next_range!(i)
      end
    else
      next_range!(last(findmin(values)))
    end
  end
  cone = Multispan(map((π,f) -> FinFunction(π, length(f)), πs, funcs))
  Limit(cospan, cone)
end

similar_mutable(x::AbstractVector, T::Type) = similar(x, T)

function similar_mutable(x::StaticVector{N}, T::Type) where N
  # `similar` always returns an `MVector` but `setindex!(::MVector, args...)`
  # only works when the element type is a bits-type.
  isbitstype(T) ? similar(x, T) : SizedVector{N}(Vector{T}(undef, N))
end

""" Limit of free diagram of FinSets.

See `CompositePullback` for a very similar construction.
"""
struct FinSetFreeDiagramLimit{Ob<:FinSet, Diagram<:FreeDiagram{Ob},
                              Cone<:Multispan{Ob}, Prod<:Product{Ob},
                              Incl<:FinFunction} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  incl::Incl # Inclusion for the "multi-equalizer" in general formula.
end

function limit(d::FreeDiagram{<:FinSet{Int}})
  # Uses the general formula for limits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.1.22 / Equation 5.16).
  prod = product(ob(d))
  n, πs = length(ob(prod)), legs(prod)
  ι = FinFunction(filter(1:n) do i
    all(begin
          s, t, h = src(d,e), tgt(d,e), hom(d,e)
          h(πs[s](i)) == πs[t](i)
        end for e in edges(d))
    end, n)
  cone = Multispan(dom(ι), [compose(ι,πs[i]) for i in vertices(d)])
  FinSetFreeDiagramLimit(d, cone, prod, ι)
end

function universal(lim::FinSetFreeDiagramLimit, cone::Multispan{<:FinSet{Int}})
  ι = collect(lim.incl)
  h = universal(lim.prod, cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)],
              apex(cone), ob(lim))
end

# Colimits
##########

function colimit(Xs::EmptyDiagram{<:FinSet{Int}})
  Colimit(Xs, SMulticospan{0}(FinSet(0)))
end

function universal(colim::Initial{<:FinSet{Int}},
                   cocone::SMulticospan{0,<:FinSet{Int}})
  FinFunction(Int[], apex(cocone))
end

function colimit(Xs::ObjectPair{<:FinSet{Int}})
  m, n = length.(Xs)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Colimit(Xs, Cospan(ι1, ι2))
end

function universal(colim::BinaryCoproduct{<:FinSet{Int}},
                   cocone::Cospan{<:FinSet{Int}})
  f, g = cocone
  FinFunction(vcat(collect(f), collect(g)), ob(colim), apex(cocone))
end

function colimit(Xs::DiscreteDiagram{<:FinSet{Int}})
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0,cumsum(ns)...]
  ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
  Colimit(Xs, Multicospan(FinSet(n), ιs))
end

function universal(colim::Coproduct{<:FinSet{Int}},
                   cocone::Multicospan{<:FinSet{Int}})
  FinFunction(reduce(vcat, (collect(f) for f in cocone), init=Int[]),
              ob(colim), apex(cocone))
end

function colimit(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m, n = length(dom(pair)), length(codom(pair))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h], length(roots))
  Colimit(pair, SMulticospan{1}(coeq))
end

function colimit(para::ParallelMorphisms{<:FinSet{Int}})
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
  Colimit(para, SMulticospan{1}(coeq))
end

function universal(coeq::Coequalizer{<:FinSet{Int}},
                   cocone::SMulticospan{1,<:FinSet{Int}})
  pass_to_quotient(proj(coeq), only(cocone))
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction{Int,Int}, h::FinFunction{Int,Int})
  @assert dom(π) == dom(h)
  q = zeros(Int, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      @assert q[j] == h(i) "Quotient map out of coequalizer is ill-defined"
    end
  end
  @assert all(i > 0 for i in q) "Projection map is not surjective"
  FinFunction(q, codom(h))
end

function colimit(span::Multispan{<:FinSet{Int}})
  colimit(span, ComposeCoproductCoequalizer())
end

""" Colimit of free diagram of FinSets.

See `CompositePushout` for a very similar construction.
"""
struct FinSetFreeDiagramColimit{Ob<:FinSet, Diagram<:FreeDiagram{Ob},
                                Cocone<:Multicospan{Ob}, Coprod<:Coproduct{Ob},
                                Proj<:FinFunction} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  proj::Proj # Projection for the "multi-coequalizer" in general formula.
end

function colimit(d::FreeDiagram{<:FinSet{Int}})
  # Uses the general formula for colimits in Set (Leinster, 2014, Basic Category
  # Theory, Example 5.2.16).
  coprod = coproduct(ob(d))
  n, ιs = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for e in edges(d)
    s, t, h = src(d,e), tgt(d,e), hom(d,e)
    for i in dom(h)
      union!(sets, ιs[s](i), ιs[t](h(i)))
    end
  end
  h = [ find_root!(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  m = length(roots)
  π = FinFunction([ searchsortedfirst(roots, r) for r in h ], m)
  cocone = Multicospan(FinSet(m), [ compose(ιs[i],π) for i in vertices(d) ])
  FinSetFreeDiagramColimit(d, cocone, coprod, π)
end

function universal(colim::FinSetFreeDiagramColimit,
                   cocone::Multicospan{<:FinSet{Int}})
  h = universal(colim.coprod, cocone)
  pass_to_quotient(colim.proj, h)
end

end
