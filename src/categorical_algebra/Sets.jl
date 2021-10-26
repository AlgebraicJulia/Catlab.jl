""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets
export SetOb, TypeSet, PredicatedSet, SetFunction, ConstantFunction, Ob

using AutoHashEquals
using FunctionWrappers: FunctionWrapper

using ...GAT, ..Categories, ..FreeDiagrams, ..Limits
using ...Theories: Category
import ...Theories: Ob, dom, codom, id, compose, ⋅, ∘
import ..Limits: limit, universal

# Data types
############

""" Abstract type for object in the category **Set**.

The type parameter `T` is the element type of the set.

Note: This type is more abstract than the built-in Julia types `AbstractSet` and
`Set`, which are intended for data structures for finite sets. Those are
encompassed by the subtype [`FinSet`](@ref).
"""
abstract type SetOb{T} end

Base.eltype(::Type{<:SetOb{T}}) where T = T

""" A Julia data type regarded as a set.
"""
struct TypeSet{T} <: SetOb{T} end

TypeSet(T::Type) = TypeSet{T}()

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet($T)")

""" Abstract type for morphism in the category **Set**.

Every instance of `SetFunction{<:SetOb{T},<:SetOb{T′}}` is callable with
elements of type `T`, returning an element of type `T′`.

Note: This type would be better called simply `Function` but that name is
already taken by the base Julia type.
"""
abstract type SetFunction{Dom <: SetOb, Codom <: SetOb} end

SetFunction(f::Function, args...) = SetFunctionCallable(f, args...)
SetFunction(::typeof(identity), args...) = SetFunctionIdentity(args...)

show_type(io::IO, ::Type{<:SetFunction}) = print(io, "SetFunction")

""" Function in **Set** defined by a callable Julia object.
"""
@auto_hash_equals struct SetFunctionCallable{
    T,T′,Dom<:SetOb{T},Codom<:SetOb{T′}} <: SetFunction{Dom,Codom}
  # Field `func` is usually a `Function` but can be any Julia callable.
  func::FunctionWrapper{T′,Tuple{T}}
  dom::Dom
  codom::Codom

  function SetFunctionCallable(f, dom::Dom, codom::Codom) where
      {T,T′,Dom<:SetOb{T},Codom<:SetOb{T′}}
    new{T,T′,Dom,Codom}(FunctionWrapper{T′,Tuple{T}}(f), dom, codom)
  end
end

function (f::SetFunctionCallable{T,T′})(x::T)::T′ where {T,T′}
  f.func(x)
end

function Base.show(io::IO, f::F) where F <: SetFunctionCallable
  func = f.func.obj[] # Deference FunctionWrapper
  show_type(io, F)
  print(io, "($(nameof(func)), $(f.dom), $(f.codom))")
end

""" Identity function in **Set**.
"""
@auto_hash_equals struct SetFunctionIdentity{Dom} <: SetFunction{Dom,Dom}
  dom::Dom
end

function SetFunctionIdentity(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  SetFunctionIdentity(dom)
end

codom(f::SetFunctionIdentity) = f.dom

(f::SetFunctionIdentity)(x) = x

function Base.show(io::IO, f::F) where F <: SetFunctionIdentity
  show_type(io, F)
  print(io, "(identity, $(f.dom))")
end

""" Function in **Set** taking a constant value.
"""
@auto_hash_equals struct ConstantFunction{T,Value<:T,Dom,Codom<:SetOb{T}} <:
    SetFunction{Dom,Codom}
  value::Value
  dom::Dom
  codom::Codom
end

ConstantFunction(value::T, dom::SetOb) where T =
  ConstantFunction(value, dom, TypeSet{T}())

(f::ConstantFunction)(x) = f.value

# Predicated sets
#################

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
struct PredicatedSet{T} <: SetOb{T}
  predicate::FunctionWrapper{Bool,Tuple{T}}

  PredicatedSet{T}(f) where T = new{T}(FunctionWrapper{Bool,Tuple{T}}(f))
end

PredicatedSet(T::Type, f) = PredicatedSet{T}(f)

function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedSet{T}) where T
  func = s.predicate.obj[] # Deference FunctionWrapper
  print(io, "PredicatedSet($T, $(nameof(func)))")
end

const PredicatedFunction{T,T′} =
  SetFunctionCallable{T,T′,PredicatedSet{T},PredicatedSet{T′}}

function (f::PredicatedFunction{T,T′})(x::T)::T′ where {T,T′}
  dom(f)(x) || error("Predicate not satisfied on input: $x")
  y = f.func(x)
  codom(f)(y) || error("Predicate not satisfied on output: $y")
  y
end

# Category of sets
##################

""" Category of sets and functions.
"""
@instance Category{SetOb, SetFunction} begin
  dom(f::SetFunction) = f.dom
  codom(f::SetFunction) = f.codom

  id(A::SetOb) = SetFunction(identity, A, A)

  function compose(f::SetFunction, g::SetFunction)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    compose_id(f, g)
  end
end

@inline compose_id(f::SetFunction, g::SetFunction) = do_compose(f, g)
@inline compose_id(f::SetFunction, ::SetFunctionIdentity) = f
@inline compose_id(::SetFunctionIdentity, g::SetFunction) = g
@inline compose_id(f::SetFunctionIdentity, ::SetFunctionIdentity) = f

do_compose(f::SetFunction, g::SetFunction) = SetFunction(g∘f, dom(f), codom(g))
do_compose(f::SetFunction, c::ConstantFunction) =
  ConstantFunction(c.value, dom(f), codom(c))
do_compose(c::ConstantFunction, f::SetFunction) =
  ConstantFunction(f(c.value), dom(c), codom(f))
do_compose(c::ConstantFunction, d::ConstantFunction) =
  ConstantFunction(d.value, dom(c), codom(d))

@cartesian_monoidal_instance SetOb SetFunction

""" Forgetful functor Ob: Cat → Set.

Sends a category to its set of objects and a functor to its object map.
"""
Ob(::TypeCat{T}) where T = TypeSet{T}()

# Limits
########

limit(Xs::EmptyDiagram{<:TypeSet}) =
  Limit(Xs, SMultispan{0}(TypeSet(Nothing)))

universal(lim::Terminal{TypeSet{Nothing}}, span::SMultispan{0,<:SetOb}) =
  ConstantFunction(nothing, apex(span), ob(lim))

function limit(Xs::ObjectPair{<:TypeSet})
  X1, X2 = Xs
  X = TypeSet(Tuple{eltype(X1),eltype(X2)})
  π1, π2 = SetFunction(first, X, X1), SetFunction(last, X, X2)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::BinaryProduct{<:TypeSet}, span::Span{<:SetOb})
  f, g = span
  SetFunction(x -> (f(x),g(x)), apex(span), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:TypeSet})
  X = TypeSet(Tuple{map(eltype, Xs)...})
  πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(Xs) ]
  Limit(Xs, Multispan(X, πs))
end

function universal(lim::Product{<:TypeSet}, span::Multispan{<:SetOb})
  @assert length(cone(lim)) == length(span)
  fs = Tuple(legs(span))
  SetFunction(x -> map(f -> f(x), fs), apex(span), ob(lim))
end

function limit(cospan::Multicospan{<:TypeSet})
  eltype(apex(cospan)) == Nothing ? product(feet(cospan)) :
    error("Pullbacks of TypeSets that are not products are not supported")
end

end
