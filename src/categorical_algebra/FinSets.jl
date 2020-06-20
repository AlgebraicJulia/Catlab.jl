module FinSets
export FinOrd, FinOrdFunction, force, terminal, product, equalizer, pullback,
  initial, coproduct, coequalizer, pushout

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root

using ...GAT
using ...Theories: Category
using ..ShapeDiagrams
import ...Theories: dom, codom, id, compose, ⋅, ∘,
  terminal, product, equalizer, initial, coproduct, coequalizer

# Data types
############

""" Finite ordinal (natural number).

An object in the category of finite ordinals, which is the skeleton of the
category of finite sets.
"""
@auto_hash_equals struct FinOrd{T<:Integer}
  n::T
end

""" Function between sets in the form of finite ordinals.

A morphism in the category of finite ordinals, which is the skeleton of the
category of finite sets.

In this data structure, the field `func` representing the function can have any
Julia type `T`, provided that `FinOrdFunction{T}` is callable. Usually, this
object will be an ordinary Julia function or an abstract vector. In the latter
case, the function (1↦1, 2↦3, 3↦2, 4↦3) is represented by the vector [1,3,2,3].
"""
@auto_hash_equals struct FinOrdFunction{F,T<:Integer}
  func::F
  dom::T
  codom::T
end
FinOrdFunction(f::AbstractVector) = FinOrdFunction(f, maximum(f))
FinOrdFunction(f::AbstractVector, codom::Integer) =
  FinOrdFunction(f, length(f), codom)

# Function objects are callable.
(f::FinOrdFunction)(i::Integer) = f.func(i)
(f::FinOrdFunction{<:AbstractVector})(i::Integer) = f.func[i]
(f::FinOrdFunction{typeof(id)})(i::Integer) = i

""" Force evaluation of function, yielding the vector representation.
"""
force(f::FinOrdFunction) = FinOrdFunction(map(f, 1:f.dom), f.codom)
force(f::FinOrdFunction{<:AbstractVector}) = f

# Category of finite ordinals
#############################

@instance Category(FinOrd, FinOrdFunction) begin
  dom(f::FinOrdFunction) = FinOrd(f.dom)
  codom(f::FinOrdFunction) = FinOrd(f.codom)
  
  id(A::FinOrd) = FinOrdFunction(id, A.n, A.n)
  
  function compose(f::FinOrdFunction, g::FinOrdFunction)
    @assert f.codom == g.dom
    FinOrdFunction(compose_functions(f.func, g.func), f.dom, g.codom)
  end
end

compose_functions(f,g) = as_function(g) ∘ as_function(f)
compose_functions(::typeof(id), g) = g
compose_functions(f, ::typeof(id)) = f
compose_functions(::typeof(id), ::typeof(id)) = id
compose_functions(f::AbstractVector, g::AbstractVector) = g[f]

as_function(f) = f
as_function(f::AbstractVector) = x -> f[x]

# Limits
########

terminal(::Type{FinOrd}) = FinOrd(1)
terminal(::Type{FinOrd{T}}) where T = FinOrd(one(T))

function product(A::FinOrd, B::FinOrd)
  m, n = A.n, B.n
  indices = CartesianIndices((m, n))
  π1 = FinOrdFunction(i -> indices[i][1], m*n, m)
  π2 = FinOrdFunction(i -> indices[i][2], m*n, n)
  Span(π1, π2)
end

function equalizer(f::FinOrdFunction, g::FinOrdFunction)
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m = f.dom
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
initial(::Type{FinOrd{T}}) where T = FinOrd(zero(T))

function coproduct(A::FinOrd, B::FinOrd)
  m, n = A.n, B.n
  ι1 = FinOrdFunction(1:m, m, m+n)
  ι2 = FinOrdFunction(m+1:m+n, n, m+n)
  Cospan(ι1, ι2)
end

function coequalizer(f::FinOrdFunction, g::FinOrdFunction)
  @assert dom(f) == dom(g) && codom(f) == codom(g)
  m, n = f.dom, f.codom
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
