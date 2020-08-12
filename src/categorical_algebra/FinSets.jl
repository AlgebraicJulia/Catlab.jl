""" Computing in the category of finite sets and functions.
"""
module FinSets
export FinSet, FinFunction, FinFunctionCallable, FinFunctionVector, force,
  terminal, product, equalizer, pullback, limit,
  initial, coproduct, coequalizer, pushout, colimit

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  terminal, product, equalizer, initial, coproduct, coequalizer
using ..ShapeDiagrams

# Category of finite sets
#########################

""" Abstract type for objects in a category that are sets.

An implementation detail used to control method dispatch. Concrete subtypes
include `FinSet` and `FinRel`.
"""
abstract type AbstractSetOb{S} end

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
@auto_hash_equals struct FinSet{S} <: AbstractSetOb{S}
  set::S
end

iterable(s::FinSet{Int}) = 1:s.set
iterable(s::FinSet{<:AbstractSet}) = s.set

""" Function between finite sets.

The function can be defined implicitly by an arbitrary Julia function, in which
case it is evaluated lazily, or explictly by a vector of integers. In the latter
case, the function (1↦1, 2↦3, 3↦2, 4↦3), for example, is represented by the
vector [1,3,2,3].
"""
abstract type FinFunction{S} end

FinFunction(f::Function, args...) = FinFunctionCallable(f, args...)
FinFunction(f::AbstractVector, args...) = FinFunctionVector(f, args...)

""" Function in FinSet defined by a callable Julia object.

To be evaluated lazily unless forced.
"""
@auto_hash_equals struct FinFunctionCallable{S} <: FinFunction{S}
  func::Any # Usually `Function` but can be any Julia callable.
  dom::FinSet{S}
  codom::FinSet{S}
end
FinFunctionCallable(f::Function, dom::Int, codom::Int) =
  FinFunctionCallable(f, FinSet(dom), FinSet(codom))

(f::FinFunctionCallable)(x) = f.func(x)

""" Function in FinSet represented explicitly by a vector.

The elements of the set are assumed to be {1,...,n}.
"""
@auto_hash_equals struct FinFunctionVector{T<:AbstractVector{Int}} <: FinFunction{Int}
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

compose_impl(f::FinFunction, g::FinFunction) = g ∘ f
compose_impl(f::FinFunctionVector, g::FinFunctionVector) = g.func[f.func]

# Limits
########

terminal(::Type{FinSet{Int}}) = FinSet(1)

function product(A::FinSet{Int}, B::FinSet{Int})
  m, n = length(A), length(B)
  indices = CartesianIndices((m, n))
  π1 = FinFunction(i -> indices[i][1], m*n, m)
  π2 = FinFunction(i -> indices[i][2], m*n, n)
  Span(π1, π2)
end

function product(Xs::AbstractVector{FinSet{Int}})
  ns = length.(Xs)
  indices = CartesianIndices(tuple(ns...))
  apex = prod(ns)
  πs = [FinFunction(i -> indices[i][j],apex,ns[j]) for j in 1:length(ns)]
  Cone(FinSet(apex), πs)
end

function equalizer(f::FinFunction{Int}, g::FinFunction{Int})
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m = length(dom(f))
  FinFunction(filter(i -> f(i) == g(i), 1:m), m)
end

function equalizer(fs::AbstractVector{<:FinFunction{Int}})
  @assert length(fs) >= 1
  f1 = fs[1]
  frest = fs[2:end]
  @assert all(dom(f) == dom(f1) && codom(f) == codom(f1) for f in frest)
  m = length(dom(f1))
  FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m),m)
end

""" Pullback of cospan of functions between finite sets.

TODO: This logic is completely generic. Make it independent of FinSet.
"""
function pullback(cospan::Cospan{<:FinFunction,<:FinFunction})
  f, g = left(cospan), right(cospan)
  prod = product(dom(f), dom(g))
  π1, π2 = left(prod), right(prod)
  eq = equalizer(π1⋅f, π2⋅g)
  Span(eq⋅π1, eq⋅π2)
end

function limit(d::Diagram{FinSet{Int}, <:FinFunction{Int}})
  p = product(d.obs)
  n = length(apex(p))
  satisfy((s,t,g),x) = g(leg(p,s)(x)) == leg(p,t)(x)
  f = FinFunction(filter(i -> all(satisfy(h,i) for h in d.homs), 1:n), n)
  Cone(dom(f),[compose(f,leg(p,i)) for i in 1:length(d.obs)])
end


# Colimits
##########

initial(::Type{FinSet{Int}}) = FinSet(0)

function coproduct(A::FinSet{Int}, B::FinSet{Int})
  m, n = length(A), length(B)
  ι1 = FinFunction(1:m, m, m+n)
  ι2 = FinFunction(m+1:m+n, n, m+n)
  Cospan(ι1, ι2)
end

function coproduct(Xs::AbstractVector{FinSet{Int}})
  ns = length.(Xs)
  base = sum(ns)
  offsets = [0,cumsum(ns)...]
  πs = [FinFunction((1:ns[j]) .+ offsets[j],ns[j],base) for j in 1:length(ns)]
  Cocone(FinSet(base), πs)
end

function coequalizer(f::FinFunction{Int}, g::FinFunction{Int})
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m, n = length(dom(f)), length(codom(f))
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  FinFunction([ searchsortedfirst(roots, r) for r in h], length(roots))
end

function coequalizer(fs::AbstractVector{<:FinFunction{Int}})
  @assert length(fs) >= 1
  f1 = fs[1]
  frest = fs[2:end]
  @assert all(dom(f) == dom(f1) && codom(f) == codom(f1) for f in frest)
  m,n = length(dom(f1)), length(codom(f1))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  FinFunction([searchsortedfirst(roots, r) for r in h], length(roots))
end

""" Pushout of span of functions between finite sets.

TODO: This logic is completely generic. Make it independent of FinSet.
"""
function pushout(span::Span{<:FinFunction,<:FinFunction})
  f, g = left(span), right(span)
  coprod = coproduct(codom(f), codom(g))
  ι1, ι2 = left(coprod), right(coprod)
  coeq = coequalizer(f⋅ι1, g⋅ι2)
  Cospan(ι1⋅coeq, ι2⋅coeq)
end

function colimit(d::Diagram{FinSet{Int}, <:FinFunction{Int}})
  cp = coproduct(d.obs)
  n = length(base(cp))
  sets = IntDisjointSets(n)
  for (s,t,h) in d.homs
    for i in d.obs[s]
      union!(sets,leg(cp,s)(i),leg(cp,t)(h(i)))
    end
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  m = length(roots)
  f = FinFunction([searchsortedfirst(roots, r) for r in h], m)
  Cocone(FinSet(m),[compose(leg(cp,i),f) for i in 1:length(d.obs)])
end

end
