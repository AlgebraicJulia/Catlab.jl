module FinSets
export FinOrd, FinOrdFunction, pushout

using AutoHashEquals
using DataStructures: IntDisjointSets, union!, find_root

using ...GAT
using ...Theories: Category
using ..ShapeDiagrams
import ...Theories: dom, codom, compose, ⋅, ∘, id

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
will be an ordinary Julia function or a vector. In the latter case, the function
(1↦1, 2↦3, 3↦2, 4↦3) would be represented by the vector [1,3,2,3].
"""
@auto_hash_equals struct FinOrdFunction{F,T<:Integer}
  func::F
  dom::T
  codom::T
end
FinOrdFunction(f::AbstractVector) = FinOrdFunction(f, max(f))
FinOrdFunction(f::AbstractVector, codom::Integer) =
  FinOrdFunction(f, length(f), codom)

# Function objects are callable.
(f::FinOrdFunction)(i::Integer) = f.func(i)
(f::FinOrdFunction{<:AbstractVector})(i::Integer) = f.func[i]

# Category of finite ordinals
#############################

@instance Category(FinOrd, FinOrdFunction) begin
  dom(f::FinOrdFunction) = FinOrd(f.dom)
  codom(f::FinOrdFunction) = FinOrd(f.codom)
  
  id(A::FinOrd) = FinOrdFunction(identity, A.n, A.n)
  
  function compose(f::FinOrdFunction, g::FinOrdFunction)
    @assert f.codom == g.dom
    FinOrdFunction(compose_functions(f.func, g.func), f.dom, g.codom)
  end
end

compose_functions(f,g) = g∘f # By default, Julia's built-in compose
compose_functions(::typeof(identity), g) = g
compose_functions(f, ::typeof(identity)) = f
compose_functions(::typeof(identity), ::typeof(identity)) = identity
compose_functions(f::AbstractVector, g::AbstractVector) = g[f]

# Limits and colimits
#####################

""" Pushout of span of functions between finite sets.

Returns a cospan whose legs are the inclusions into the quotient set.
"""
function pushout(span::Span{<:FinOrdFunction,<:FinOrdFunction})
  f, g = left(span), right(span)
  m, n = f.codom, g.codom
  sets = IntDisjointSets(m+n)
  for i in 1:f.dom
    union!(sets, f(i), m + g(i))
  end
  
  h = [ find_root(sets, i) for i in 1:m ]
  k = [ find_root(sets, m+i) for i in 1:n ]
  roots = unique!([h; k])
  inv_roots = Dict(root => i for (i, root) in enumerate(roots))
  h = FinOrdFunction([ inv_roots[root] for root in h ], length(roots))
  k = FinOrdFunction([ inv_roots[root] for root in k ], length(roots))
  Cospan(h, k)
end

end
