""" Computing in the category of finite sets and functions.
"""
module FinSets
export FinSet, FinFunction, FinFunctionCallable, FinFunctionVector, force

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root
import FunctionWrappers: FunctionWrapper
using StaticArrays: StaticVector, SVector, @SVector

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘
using ..FreeDiagrams, ..Limits
import ..Limits: terminal, product, pair, equalizer, pullback, limit,
  initial, coproduct, copair, coequalizer, pushout, colimit, factorize

# Category of finite sets
#########################

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

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the latter
case, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented by the
vector [1,3,2,3].
"""
abstract type FinFunction{S,T} end

FinFunction(f::Function, args...) = FinFunctionCallable(f, args...)
FinFunction(f::AbstractVector, args...) = FinFunctionVector(f, args...)

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
  FinFunctionCallable(FunctionWrapper{T,Tuple{T}}(f),dom,codom)

(f::FinFunctionCallable)(x) = f.func(x)

""" Function in FinSet represented explicitly by a vector.

The elements of the set are assumed to be {1,...,n}.
"""
@auto_hash_equals struct FinFunctionVector{T<:AbstractVector{Int}} <: FinFunction{Int,Int}
  func::T
  codom::Int
end
FinFunctionVector(f::AbstractVector) = FinFunctionVector(f, maximum(f))

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

(f::FinFunctionVector)(x) = f.func[x]

""" Force evaluation of lazy function or relation.
"""
force(f::FinFunction{Int}) = FinFunctionVector(map(f, dom(f)), codom(f))
force(f::FinFunctionVector) = f

Base.collect(f::FinFunction) = force(f).func

""" Category of finite sets and functions.
"""
@instance Category{FinSet, FinFunction} begin
  dom(f::FinFunction) = f.dom
  codom(f::FinFunction) = f.codom
  
  id(A::FinSet) = FinFunction(identity, A, A)
  
  function compose(f::FinFunction, g::FinFunction)
    @assert codom(f) == dom(g)
    FinFunction(compose_impl(f,g), dom(f), codom(g))
  end
end

compose_impl(f::FinFunction{S,T}, g::FinFunction{S,T}) where {S,T} = g ∘ f
compose_impl(f::FinFunctionVector, g::FinFunctionVector) = g.func[f.func]

# Limits
########

function product(Xs::StaticVector{0,<:FinSet{Int}})
  Limit(Xs, Multispan(FinSet(1), @SVector FinFunction{Int}[]))
end

function product(Xs::StaticVector{2,<:FinSet{Int}})
  m, n = length.(Xs)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Limit(Xs, Span(π1, π2))
end

function pair(prod::BinaryProduct{<:FinSet{Int}}, fs::Span{<:FinSet{Int}})
  f, g = fs
  m, n = length.(codom.(fs))
  indices = LinearIndices((m, n))
  FinFunction(i -> indices[f(i),g(i)], apex(fs), ob(prod))
end

function product(Xs::AbstractVector{<:FinSet{Int}})
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = [FinFunction(i -> indices[i][j], n, ns[j]) for j in 1:length(ns)]
  Limit(Xs, Multispan(FinSet(n), πs))
end

function pair(prod::Product{<:FinSet{Int}}, fs::Multispan{<:FinSet})
  ns = length.(codom.(fs))
  indices = LinearIndices(Tuple(ns))
  FinFunction(i -> indices[(f(i) for f in fs)...], apex(fs), ob(prod))
end

function equalizer(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m = length(dom(pair))
  eq = FinFunction(filter(i -> f(i) == g(i), 1:m), m)
  Limit(pair, Multispan(SVector(eq)))
end

function equalizer(para::ParallelMorphisms{<:FinSet{Int}})
  @assert length(para) >= 1
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(para, Multispan(SVector(eq)))
end

function limit(d::FreeDiagram{<:FinSet{Int}})
  p = product(ob(d))
  n, leg = length(ob(p)), legs(p)
  satisfy(e,x) = hom(d,e)(leg[src(d,e)](x)) == leg[tgt(d,e)](x)
  f = FinFunction(filter(i -> all(satisfy(e,i) for e in edges(d)), 1:n), n)
  Limit(d, Multispan(dom(f), [compose(f,leg[i]) for i in vertices(d)]))
end

# Colimits
##########

function coproduct(Xs::StaticVector{0,<:FinSet{Int}})
  Colimit(Xs, Multicospan(FinSet(0), @SVector FinFunction{Int}[]))
end

function coproduct(Xs::StaticVector{2,<:FinSet{Int}})
  m, n = length.(Xs)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Colimit(Xs, Cospan(ι1, ι2))
end

function coproduct(Xs::AbstractVector{<:FinSet{Int}})
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0,cumsum(ns)...]
  ιs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],n) for j in 1:length(ns)]
  Colimit(Xs, Multicospan(FinSet(n), ιs))
end

function coequalizer(pair::ParallelPair{<:FinSet{Int}})
  f, g = pair
  m, n = length(dom(pair)), length(codom(pair))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  coeq = FinFunction([ searchsortedfirst(roots, r) for r in h], length(roots))
  Colimit(pair, Multicospan(SVector(coeq)))
end

function coequalizer(para::ParallelMorphisms{<:FinSet{Int}})
  @assert length(para) >= 1
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
  coeq = FinFunction([searchsortedfirst(roots, r) for r in h], length(roots))
  Colimit(para, Multicospan(SVector(coeq)))
end

function colimit(d::FreeDiagram{<:FinSet{Int}})
  cp = coproduct(ob(d))
  n, leg = length(ob(cp)), legs(cp)
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
  f = FinFunction([searchsortedfirst(roots, r) for r in h], m)
  Colimit(d, Multicospan(FinSet(m), [compose(leg[i],f) for i in vertices(d)]))
end

end
