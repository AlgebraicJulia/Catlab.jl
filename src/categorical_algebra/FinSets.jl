""" Computing in the category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinOrd, FinOrdFunction, force, terminal, product, equalizer, pullback,
  initial, coproduct, coequalizer, pushout

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  terminal, product, equalizer, initial, coproduct, coequalizer
using ..ShapeDiagrams

# Data types
############

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
@auto_hash_equals struct FinOrdFunctionLazy <: FinOrdFunction
  func::Function
  dom::Int
  codom::Int
end
(f::FinOrdFunctionLazy)(i) = f.func(i)

FinOrdFunction(f::Function, dom::Int, codom::Int) =
  FinOrdFunctionLazy(f, dom, codom)

""" Function in FinOrd represented explicitly by a vector.
"""
@auto_hash_equals struct FinOrdFunctionMap{T<:AbstractVector{Int}} <: FinOrdFunction
  func::T
  codom::Int
end
(f::FinOrdFunctionMap)(i) = f.func[i]

FinOrdFunction(f::AbstractVector) = FinOrdFunctionMap(f, maximum(f))
FinOrdFunction(f::AbstractVector, codom::Int) = FinOrdFunctionMap(f, codom)

function FinOrdFunction(f::AbstractVector, dom::Int, codom::Int)
  @assert length(f) == dom
  FinOrdFunctionMap(f, codom)
end

""" Force evaluation of function, yielding the vector representation.
"""
force(f::FinOrdFunction) = FinOrdFunctionMap(map(f, 1:dom(f).n), codom(f).n)
force(f::FinOrdFunctionMap) = f

# Category of finite ordinals
#############################

@instance Category(FinOrd, FinOrdFunction) begin
  dom(f::FinOrdFunction) = FinOrd(f.dom)
  codom(f::FinOrdFunction) = FinOrd(f.codom)
  
  id(A::FinOrd) = FinOrdFunction(identity, A, A)
  
  function compose(f::FinOrdFunction, g::FinOrdFunction)
    @assert codom(f) == dom(g)
    FinOrdFunction(compose_impl(f,g), dom(f), codom(g))
  end
end

dom(f::FinOrdFunctionMap) = FinOrd(length(f.func))
compose_impl(f::FinOrdFunction, g::FinOrdFunction) = g ∘ f
compose_impl(f::FinOrdFunctionMap, g::FinOrdFunctionMap) = g.func[f.func]

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

function equalizer(f::FinOrdFunction, g::FinOrdFunction)
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m = dom(f).n
  FinOrdFunction(filter(i -> f(i) == g(i), 1:m), m)
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

# Colimits
##########

initial(::Type{FinOrd}) = FinOrd(0)

function coproduct(A::FinOrd, B::FinOrd)
  m, n = A.n, B.n
  ι1 = FinOrdFunction(1:m, m, m+n)
  ι2 = FinOrdFunction(m+1:m+n, n, m+n)
  Cospan(ι1, ι2)
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

end
