""" Computing in the category of finite sets and functions.
"""
module FinSets
export FinSet, FinFunction, FinFunctionCallable, FinFunctionVector, force

using Compat: only

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root
import FunctionWrappers: FunctionWrapper

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘
using ..FreeDiagrams, ..Limits
import ..Limits: limit, colimit, universal

# Data types
############

""" Abstract type for objects in a category that are sets.

An implementation detail used to control method dispatch. Concrete subtypes
include `FinSet` and `FinRel`.
"""
abstract type AbstractSetOb{S,T} end

Base.eltype(::Type{AbstractSetOb{S}}) where S = eltype(S)
Base.iterate(s::AbstractSetOb, args...) = iterate(iterable(s), args...)
Base.length(s::AbstractSetOb) = length(iterable(s))
Base.in(s::AbstractSetOb, elem) = in(s, iterable(s))

""" Finite set.

This generic type encompasses the category **FinSet** of finite sets and
functions, through types `FinSet{S} where S <: AbstractSet`, as well as the
skeleton of this category, through the type `FinSet{Int}`. In the latter case,
the object `FinSet(n)` represents the set {1,...,n}.
"""
@auto_hash_equals struct FinSet{S,T} <: AbstractSetOb{S,T}
  set::S
end

FinSet(n::Int) = FinSet{Int,Int}(n)
FinSet(set::S) where {T,S<:AbstractSet{T}} = FinSet{S,T}(set)
iterable(s::FinSet{Int}) = 1:s.set
iterable(s::FinSet{<:AbstractSet}) = s.set

Base.show(io::IO, s::FinSet) = print(io, "FinSet($(s.set))")

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the latter
case, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented by the
vector [1,3,2,3].
"""
abstract type FinFunction{S,T} end

FinFunction(f::Function, args...) = FinFunctionCallable(f, args...)
FinFunction(f::AbstractVector, args...) = FinFunctionVector(f, args...)
FinFunction(::typeof(identity), args...) = FinFunctionIdentity(args...)

""" Function in FinSet defined by a callable Julia object.

To be evaluated lazily unless forced.
"""
@auto_hash_equals struct FinFunctionCallable{S,T} <: FinFunction{S,T}
  func::FunctionWrapper{T,Tuple{T}} # Usually `Function` but can be any Julia callable.
  dom::FinSet{S,T}
  codom::FinSet{S,T}
end
FinFunctionCallable(f::Function, dom::Int, codom::Int) =
  FinFunctionCallable(FunctionWrapper{Int,Tuple{Int}}(f), FinSet(dom), FinSet(codom))
FinFunctionCallable(f::Function, dom::FinSet{S,T}, codom::FinSet{S,T}) where {S,T} =
  FinFunctionCallable(FunctionWrapper{T,Tuple{T}}(f), dom, codom)

function Base.show(io::IO, f::FinFunctionCallable)
  func = f.func.obj[] # Deference FunctionWrapper
  print(io, "FinFunction($(nameof(func)), $(f.dom), $(f.codom))")
end

(f::FinFunctionCallable)(x) = f.func(x)

""" Function in FinSet represented explicitly by a vector.

The elements of the set are assumed to be {1,...,n}.
"""
@auto_hash_equals struct FinFunctionVector{T<:AbstractVector{Int}} <: FinFunction{Int,Int}
  func::T
  codom::Int
end
FinFunctionVector(f::AbstractVector) =
  FinFunctionVector(f, isempty(f) ? 0 : maximum(f))

function FinFunctionVector(f::AbstractVector, dom::Int, codom::Int)
  length(f) == dom || error("Length of vector $f does not match domain $dom")
  FinFunctionVector(f, codom)
end

FinFunctionVector(f::AbstractVector, codom::FinSet{Int}) =
  FinFunctionVector(f, length(codom))
FinFunctionVector(f::AbstractVector, dom::FinSet{Int}, codom::FinSet{Int}) =
  FinFunctionVector(f, length(dom), length(codom))

dom(f::FinFunctionVector) = FinSet(length(f.func))
codom(f::FinFunctionVector) = FinSet(f.codom)

Base.show(io::IO, f::FinFunctionVector) =
  print(io, "FinFunction($(f.func), $(length(f.func)), $(f.codom))")

(f::FinFunctionVector)(x) = f.func[x]

""" Force evaluation of lazy function or relation.
"""
force(f::FinFunction{Int}) = FinFunctionVector(map(f, dom(f)), codom(f))
force(f::FinFunctionVector) = f

Base.collect(f::FinFunction) = force(f).func

""" Identity function in FinSet.
"""
@auto_hash_equals struct FinFunctionIdentity{S,T} <: FinFunction{S,T}
  dom::FinSet{S,T}
end

function FinFunctionIdentity(dom, codom)
  @assert dom == codom
  FinFunctionIdentity(dom)
end
FinFunctionIdentity(n::Int) = FinFunctionIdentity(FinSet(n))

dom(f::FinFunctionIdentity) = f.dom
codom(f::FinFunctionIdentity) = f.dom

Base.show(io::IO, f::FinFunctionIdentity) =
  print(io, "FinFunction(identity, $(f.dom))")

(f::FinFunctionIdentity)(x) = x

# Category of finite sets
#########################

""" Category of finite sets and functions.
"""
@instance Category{FinSet, FinFunction} begin
  dom(f::FinFunction) = f.dom
  codom(f::FinFunction) = f.codom
  
  id(A::FinSet) = FinFunction(identity, A, A)
  
  function compose(f::FinFunction, g::FinFunction)
    @assert codom(f) == dom(g)
    compose_impl(f, g)
  end
end

compose_impl(f::FinFunction{S,T}, g::FinFunction{S,T}) where {S,T} =
  FinFunction(g ∘ f, dom(f), codom(g))
compose_impl(f::FinFunctionVector, g::FinFunctionVector) =
  FinFunctionVector(g.func[f.func], g.codom)

compose_impl(f::FinFunction, ::FinFunctionIdentity) = f
compose_impl(::FinFunctionIdentity, f::FinFunction) = f
compose_impl(f::FinFunctionIdentity, ::FinFunctionIdentity) = f

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
  FinFunction(Int[only(searchsorted(ι, i)) for i in collect(h)], length(ι))
end

limit(cospan::Multicospan{<:FinSet{Int}}) = composite_pullback(cospan)

function limit(d::FreeDiagram{<:FinSet{Int}})
  p = product(ob(d))
  n, leg = length(ob(p)), legs(p)
  satisfy(e,x) = hom(d,e)(leg[src(d,e)](x)) == leg[tgt(d,e)](x)
  f = FinFunction(filter(i -> all(satisfy(e,i) for e in edges(d)), 1:n), n)
  Limit(d, Multispan(dom(f), [compose(f,leg[i]) for i in vertices(d)]))
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
  h = [ find_root(sets, i) for i in 1:n ]
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
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
  Colimit(para, SMulticospan{1}(coeq))
end

function universal(coeq::Coequalizer{<:FinSet{Int}},
                   cocone::SMulticospan{1,<:FinSet{Int}})
  q = zeros(Int, length(ob(coeq)))
  π = proj(coeq)
  h = only(cocone)
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      @assert q[j] == h(i) "Quotient map out of coequalizer is ill-defined"
    end
  end
  FinFunction(q, codom(h))
end

colimit(span::Multispan{<:FinSet{Int}}) = composite_pushout(span)

function colimit(d::FreeDiagram{<:FinSet{Int}})
  coprod = coproduct(ob(d))
  n, leg = length(ob(coprod)), legs(coprod)
  sets = IntDisjointSets(n)
  for e in edges(d)
    s, t, h = src(d,e), tgt(d,e), hom(d,e)
    for i in dom(h)
      union!(sets, leg[s](i), leg[t](h(i)))
    end
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  m = length(roots)
  f = FinFunction([ searchsortedfirst(roots, r) for r in h ], m)
  Colimit(d, Multicospan(FinSet(m), [ compose(leg[i],f) for i in vertices(d) ]))
end

end
