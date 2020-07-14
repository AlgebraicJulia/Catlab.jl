""" Computing in the category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinOrd, FinOrdFunction, FinOrdFunc, FinOrdVector, force,
  terminal, product, equalizer, pullback, limit,
  initial, coproduct, coequalizer, pushout, colimit

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  terminal, product, equalizer, initial, coproduct, coequalizer
using ..ShapeDiagrams

# Category of finite ordinals
#############################

""" Finite ordinal (natural number).

An object in the category of finite ordinals, which is the skeleton of the
category of finite sets.
"""
@auto_hash_equals struct FinOrd
  n::Int
end

""" Function between sets in the form of finite ordinals.

A morphism in the category of finite ordinals, which is the skeleton of the
category of finite sets. The function can be defined implicitly by an arbitrary
Julia function, in which case it is evaluated lazily, or explictly by a vector
of integers. In the latter case, the function (1↦1, 2↦3, 3↦2, 4↦3), for example,
is represented by the vector [1,3,2,3].
"""
abstract type FinOrdFunction end

FinOrdFunction(f, dom::FinOrd, codom::FinOrd) =
  FinOrdFunction(f, dom.n, codom.n)

""" Function in FinOrd defined by an arbitrary Julia function.

To be evaluated lazily unless forced.
"""
@auto_hash_equals struct FinOrdFunc <: FinOrdFunction
  func::Function
  dom::Int
  codom::Int
end
FinOrdFunction(f::Function, dom::Int, codom::Int) =
  FinOrdFunc(f, dom, codom)

(f::FinOrdFunc)(x) = f.func(x)

""" Function in FinOrd represented explicitly by a vector.
"""
@auto_hash_equals struct FinOrdVector{T<:AbstractVector{Int}} <: FinOrdFunction
  func::T
  codom::Int
end
FinOrdFunction(f::AbstractVector) = FinOrdVector(f, maximum(f))
FinOrdFunction(f::AbstractVector, codom::Int) = FinOrdVector(f, codom)

function FinOrdFunction(f::AbstractVector, dom::Int, codom::Int)
  @assert length(f) == dom
  FinOrdVector(f, codom)
end

(f::FinOrdVector)(x) = f.func[x]

""" Force evaluation of lazy function or relation.
"""
force(f::FinOrdFunction) = FinOrdVector(map(f, 1:dom(f).n), codom(f).n)
force(f::FinOrdVector) = f

Base.collect(f::FinOrdFunction) = force(f).func

""" Category of finite ordinals and functions.
"""
@instance Category(FinOrd, FinOrdFunction) begin
  dom(f::FinOrdFunction) = FinOrd(f.dom)
  codom(f::FinOrdFunction) = FinOrd(f.codom)
  
  id(A::FinOrd) = FinOrdFunction(identity, A, A)
  
  function compose(f::FinOrdFunction, g::FinOrdFunction)
    @assert codom(f) == dom(g)
    FinOrdFunction(compose_impl(f,g), dom(f), codom(g))
  end
end

dom(f::FinOrdVector) = FinOrd(length(f.func))
compose_impl(f::FinOrdFunction, g::FinOrdFunction) = g ∘ f
compose_impl(f::FinOrdVector, g::FinOrdVector) = g.func[f.func]

# Limits
########

terminal(::Type{FinOrd}) = FinOrd(1)

function product(A::FinOrd, B::FinOrd)
  m, n = A.n, B.n
  indices = CartesianIndices((m, n))
  π1 = FinOrdFunction(i -> indices[i][1], m*n, m)
  π2 = FinOrdFunction(i -> indices[i][2], m*n, n)
  Span(π1, π2)
end

function product(Xs::Vector{<:FinOrd})
  ns = Int[X.n for X in Xs]
  indices = CartesianIndices(tuple(ns...))
  apex = prod(ns)
  πs = [FinOrdFunction(i -> indices[i][j],apex,ns[j]) for j in 1:length(ns)]
  Cone(FinOrd(apex),πs)
end

function equalizer(f::FinOrdFunction, g::FinOrdFunction)
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m = dom(f).n
  FinOrdFunction(filter(i -> f(i) == g(i), 1:m), m)
end

function equalizer(fs::Vector{<:FinOrdFunction})
  @assert length(fs) >= 1
  f1 = fs[1]
  frest = fs[2:end]
  @assert all(dom(f) == dom(f1) && codom(f) == codom(f1) for f in frest)
  m = dom(f1).n
  FinOrdFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m),m)
end

""" Pullback of cospan of functions between finite ordinals.

TODO: This logic is completely generic. Make it independent of FinOrd.
"""
function pullback(cospan::Cospan{<:FinOrdFunction,<:FinOrdFunction})
  f, g = left(cospan), right(cospan)
  prod = product(dom(f), dom(g))
  π1, π2 = left(prod), right(prod)
  eq = equalizer(π1⋅f, π2⋅g)
  Span(eq⋅π1, eq⋅π2)
end

function limit(d::Diagram{<:FinOrd, <:FinOrdFunction})
  p = product(d.obs)
  n = apex(p).n
  satisfy((s,t,g),x) = g(leg(p,s)(x)) == leg(p,t)(x)
  f = FinOrdFunction(filter(i -> all(satisfy(h,i) for h in d.homs), 1:n), n)
  Cone(dom(f),[compose(f,leg(p,i)) for i in 1:length(d.obs)])
end


# Colimits
##########

initial(::Type{FinOrd}) = FinOrd(0)

function coproduct(A::FinOrd, B::FinOrd)
  m, n = A.n, B.n
  ι1 = FinOrdFunction(1:m, m, m+n)
  ι2 = FinOrdFunction(m+1:m+n, n, m+n)
  Cospan(ι1, ι2)
end

function coproduct(Xs::Vector{<:FinOrd})
  ns = Int[X.n for X in Xs]
  base = sum(ns)
  offsets = [0,cumsum(ns)...]
  πs = [FinOrdFunction((1:ns[j]) .+ offsets[j],ns[j],base) for j in 1:length(ns)]
  Cocone(FinOrd(base),πs)
end

function coequalizer(f::FinOrdFunction, g::FinOrdFunction)
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m, n = dom(f).n, codom(f).n
  sets = IntDisjointSets(n)
  for i in 1:m
    union!(sets, f(i), g(i))
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  FinOrdFunction([ searchsortedfirst(roots, r) for r in h], length(roots))
end

function coequalizer(fs::Vector{<:FinOrdFunction})
  @assert length(fs) >= 1
  f1 = fs[1]
  frest = fs[2:end]
  @assert all(dom(f) == dom(f1) && codom(f) == codom(f1) for f in frest)
  m,n = dom(f1).n, codom(f1).n
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  FinOrdFunction([searchsortedfirst(roots, r) for r in h], length(roots))
end

""" Pushout of span of functions between finite ordinals.

TODO: This logic is completely generic. Make it independent of FinOrd.
"""
function pushout(span::Span{<:FinOrdFunction,<:FinOrdFunction})
  f, g = left(span), right(span)
  coprod = coproduct(codom(f), codom(g))
  ι1, ι2 = left(coprod), right(coprod)
  coeq = coequalizer(f⋅ι1, g⋅ι2)
  Cospan(ι1⋅coeq, ι2⋅coeq)
end

function colimit(d::Diagram{<:FinOrd, <:FinOrdFunction})
  cp = coproduct(d.obs)
  n = base(cp).n
  sets = IntDisjointSets(n)
  for (s,t,h) in d.homs
    for i in 1:d.obs[s].n
      union!(sets,leg(cp,s)(i),leg(cp,t)(h(i)))
    end
  end
  h = [ find_root(sets, i) for i in 1:n ]
  roots = unique!(sort(h))
  m = length(roots)
  f = FinOrdFunction([searchsortedfirst(roots, r) for r in h], m)
  Cocone(FinOrd(m),[compose(leg(cp,i),f) for i in 1:length(d.obs)])
end

end
