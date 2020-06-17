module FinSets
export FinOrd, FinOrdFunction

using AutoHashEquals

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, compose, ⋅, ∘, id

""" Finite ordinal (natural number).

An object in the category of finite ordinals, which is the skeleton of the
category of finite sets.
"""
@auto_hash_equals struct FinOrd{T<:Integer}
  n::T
end

""" Function between sets of form `1:n`.

A morphism in the category of finite ordinals, which is the skeleton of the
category of finite sets.

TODO: Explain data structures: functions, vectors.
"""
@auto_hash_equals struct FinOrdFunction{T<:Integer,F}
  func::F
  dom::T
  codom::T
end

FinOrdFunction(f::AbstractVector) = FinOrdFunction(f, max(f))
FinOrdFunction(f::AbstractVector, codom::Integer) =
  FinOrdFunction(f, length(f), codom)

(f::FinOrdFunction)(i::Integer) = f.func(i)
(f::FinOrdFunction{T,Vector{T}})(i::Integer) where T = f.func[i]

@instance Category(FinOrd, FinOrdFunction) begin
  dom(f::FinOrdFunction) = FinOrd(f.dom)
  codom(f::FinOrdFunction) = FinOrd(f.codom)
  
  id(A::FinOrd) = FinOrdFunction(identity, A.n, A.n)
  
  function compose(f::FinOrdFunction, g::FinOrdFunction)
    @assert f.codom == g.dom
    FinOrdFunction(compose_functions(f.func, g.func), f.dom, g.codom)
  end
end

compose_functions(f,g) = g∘f # Julia's built-in composition
compose_functions(::typeof(identity), g) = g
compose_functions(f, ::typeof(identity)) = f
compose_functions(::typeof(identity), ::typeof(identity)) = identity
compose_functions(f::AbstractVector, g::AbstractVector) = g[f]

end
