""" Categories of sets, including infinite ones, and functions.
"""
module Sets
export SetOb, TypeSet, PredicatedSet, SetFunction

using AutoHashEquals
using FunctionWrappers: FunctionWrapper

using ...GAT
using ...Theories: Category
import ...Theories: dom, codom, id, compose, ⋅, ∘

# Data types
############

""" Abstract type for object in the category **Set**.

The type parameter `T` is the element type of the set.

Note: This type is more abstract than the built-in Julia types `AbstractSet` and
`Set`, which are intended for data structures for finite sets. Those are
encompassed by the subtype [`FinSet`](@ref).
"""
abstract type SetOb{T} end

Base.eltype(::Type{SetOb{T}}) where T = T

""" A Julia data type regarded as a set.
"""
struct TypeSet{T} <: SetOb{T} end

Base.show(io::IO, ::TypeSet{T}) where T = print(io, "TypeSet{$T}()")

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

# Predicated sets
#################

""" Set defined by a predicate (boolean-valued function) on a Julia data type.
"""
struct PredicatedSet{T} <: SetOb{T}
  predicate::FunctionWrapper{Bool,Tuple{T}}

  PredicatedSet{T}(f) where T = new{T}(FunctionWrapper{Bool,Tuple{T}}(f))
end

function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
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
    compose_impl(f, g)
  end
end

compose_impl(f::SetFunction, g::SetFunction) =
  SetFunction(g ∘ f, dom(f), codom(g))
compose_impl(f::SetFunction, ::SetFunctionIdentity) = f
compose_impl(::SetFunctionIdentity, f::SetFunction) = f
compose_impl(f::SetFunctionIdentity, ::SetFunctionIdentity) = f

end
