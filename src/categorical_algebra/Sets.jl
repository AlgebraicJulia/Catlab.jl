""" Category of (possibly infinite) sets and functions.

This module defines generic types for the category of sets ([`SetOb`](@ref),
[`SetFunction`](@ref)), as well as a few basic concrete types, such as a wrapper
type to view Julia types as sets ([`TypeSet`](@ref)). Extensive support for
finite sets is provided by another module, [`FinSets`](@ref).
"""
module Sets
export SetOb, TypeSet, PredicatedSet, SetFunction, Bijection, ConstantFunction,
  Ob

using StructEquality

using ...GATs, ..Categories, ..FreeDiagrams, ..Limits
using ...Theories: ThCategory
import ...Theories: Ob, dom, codom, id, compose, ⋅, ∘
import ..Categories: show_type_constructor, show_domains
import ..Limits: limit, colimit, universal

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
Base.in(elem,::TypeSet{T}) where T = isa(elem,T)

""" Abstract type for morphism in the category **Set**.

Every instance of `SetFunction{<:SetOb{T},<:SetOb{T′}}` is callable with
elements of type `T`, returning an element of type `T′`.

Note: This type would be better called simply `Function` but that name is
already taken by the base Julia type.
"""
abstract type SetFunction{Dom <: SetOb, Codom <: SetOb} end

SetFunction(f::Function, args...) = SetFunctionCallable(f, args...)
SetFunction(::typeof(identity), args...) = IdentityFunction(args...)
SetFunction(f::SetFunction) = f

show_type_constructor(io::IO, ::Type{<:SetFunction}) = print(io, "SetFunction")

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable{
    T,T′,Dom<:SetOb{T},Codom<:SetOb{T′}} <: SetFunction{Dom,Codom}
  # Field `func` is usually a `Function` but can be any Julia callable.
  func::Any
  dom::Dom
  codom::Codom
# Code review note: the code that was here before was apparently part of
# something that was necessary in the context of an old implementation of
# `SetFunctionCallable`, but is no longer
end

function (f::SetFunctionCallable{T,T′})(x::T)::T′ where {T,T′}
  f.func(x)
end

function Base.show(io::IO, f::F) where F <: SetFunctionCallable
  show_type_constructor(io, F)
  print(io, "($(nameof(f.func)), ")
  show_domains(io, f)
  print(io, ")")
end

""" Abstract type for isomorphisms in the category **Set**.
"""
abstract type Bijection{Dom<:SetOb, Codom<:SetOb} <: SetFunction{Dom,Codom} end

Bijection(f::Function, args...) = BijectionWrapper(SetFunction(f, args...))
Bijection(f::SetFunction) = BijectionWrapper(f)
Bijection(f::SetFunction, g::SetFunction) = BijectionBimap(unwrap(f), unwrap(g))
Bijection(f::Bijection) = f

Base.inv(f::Bijection) = BijectionBimap(do_inv(f), unwrap(f))

function do_inv end

show_type_constructor(io::IO, ::Type{<:Bijection}) = print(io, "Bijection")

""" Identity function in **Set**.
"""
@struct_hash_equal struct IdentityFunction{Dom} <: Bijection{Dom,Dom}
  dom::Dom
end

function IdentityFunction(dom::SetOb, codom::SetOb)
  dom == codom || error("Domain mismatch in identity function: $dom != $codom")
  IdentityFunction(dom)
end

codom(f::IdentityFunction) = f.dom

(f::IdentityFunction)(x) = x

Base.inv(f::IdentityFunction) = f

function Base.show(io::IO, f::IdentityFunction)
  print(io, "id(")
  show_domains(io, f, codomain=false)
  print(io, ")")
end

""" An abstract type for bijections in **Set** that are implemented as wrappers
for `SetFunction` objects.

Each concrete subtype must store the wrapped `SetFunction` in the `func` field.
"""
abstract type AbsBijectionWrapper{Dom<:SetOb, Codom<:SetOb,
  F<:SetFunction{Dom,Codom}} <: Bijection{Dom,Codom} end

unwrap(f::AbsBijectionWrapper) = unwrap(f.func)
unwrap(f::SetFunction) = f

dom(f::AbsBijectionWrapper) = dom(unwrap(f))
codom(f::AbsBijectionWrapper) = codom(unwrap(f))

(f::AbsBijectionWrapper)(x) = (unwrap(f))(x)

# Developer's note: should I add in a `known_correct` parameter, asking
# the caller to decide whether the SetFunction should be checked for bijectivity?
@struct_hash_equal struct BijectionWrapper{Dom<:SetOb, Codom<:SetOb,
    F<:SetFunction{Dom,Codom}} <: AbsBijectionWrapper{Dom, Codom, F}
  func::F
end

BijectionWrapper(f::BijectionWrapper) = f

function Base.show(io::IO, f::BijectionWrapper)
  replacerules = (r"^SetFunction" => "Bijection", r"^FinFunction" => "FinBijection")
  print(io, replace(repr(f.func), replacerules...))
end

""" Bijective function in **Set** backed by a pair of (inverse) `SetFunction`s.

Methods that create `BijectionBimap`s are expected not to place objects of type
`AbsBijectionWrapper` in the `func` and `inv` fields.
"""
@struct_hash_equal struct BijectionBimap{Dom<:SetOb, Codom<:SetOb,
    F<:SetFunction{Dom,Codom}, Inv<:SetFunction} <:
    AbsBijectionWrapper{Dom, Codom, F}
  func::F
  inv::Inv
end

BijectionBimap(f::BijectionWrapper) =
  BijectionBimap(unwrap(f), unwrap(do_inv(f)))

Base.inv(f::BijectionBimap) = BijectionBimap(f.inv, f.func)

# Developer's note: this `show` method would make a little more sense if the
# constructor for `BijectionBimap` had a required keyword parameter, `inverse`.
# I tried implementing this, but Julia's multiple dispatch system doesn't take
# keyword parameters into account, and I couldn't find any way to reconcile it
# with the rest of the design.
function Base.show(io::IO, f::F) where {F<:BijectionBimap}
  show_type_constructor(io, F)
  print(io, "(")
  show(io, f.func)
  print(io, ", inverse=")
  show(io, f.inv)
  print(io, ")")
end

""" Composite of functions in **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFunction{Dom<:SetOb, Codom<:SetOb,
# Code review note: these additional restrictions, on the variables `Dom` and
# `Codom`, allow `CompositeFunction` to be recognized as a subtype of
# `SetFunction`
    F<:SetFunction{Dom,<:SetOb},G<:SetFunction{<:SetOb,Codom}} <: SetFunction{Dom,Codom}
  fst::F
  snd::G
end

Base.first(f::CompositeFunction) = f.fst
Base.last(f::CompositeFunction) = f.snd

dom(f::CompositeFunction) = dom(first(f))
codom(f::CompositeFunction) = codom(last(f))

(f::CompositeFunction)(x) = f.snd(f.fst(x))

function Base.show(io::IO, f::CompositeFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

""" Composite of bijections in **Set**.
"""
const CompositeBijection{Dom<:SetOb, Codom<:SetOb,
  F<:Bijection{Dom,<:SetOb}, G<:Bijection{<:SetOb,Codom}} =
  BijectionWrapper{Dom, Codom, CompositeFunction{Dom, Codom, F, G}}

CompositeBijection(f::Bijection, g::Bijection) =
  BijectionWrapper(CompositeFunction(f, g))

Base.first(f::CompositeBijection) = first(unwrap(f))
Base.last(f::CompositeBijection) = last(unwrap(f))

Base.inv(f::CompositeBijection) = compose(inv(last(f)), inv(first(f)))

""" Alias type for functions backed by `CompositeFunction`s.
"""
const Composite{Dom<:SetOb, Codom<:SetOb, F<:SetFunction{Dom,<:SetOb},
  G<:SetFunction{<:SetOb,Codom}} = Union{
    CompositeFunction{Dom, Codom, F, G},
    CompositeBijection{Dom, Codom, F, G}
  }

Composite(f::SetFunction, g::SetFunction) = CompositeFunction(f, g)
Composite(f::Bijection, g::Bijection) = CompositeBijection(f, g)

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction{T,Value<:T,Dom,Codom<:SetOb{T}} <:
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
  predicate::Any

  PredicatedSet{T}(f) where T = new{T}(f)
end

PredicatedSet(T::Type, f) = PredicatedSet{T}(f)

function (s::PredicatedSet{T})(x::T)::Bool where {T}
  s.predicate(x)
end

function Base.show(io::IO, s::PredicatedSet{T}) where T
  print(io, "PredicatedSet($T, $(nameof(s.predicate)))")
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
@instance ThCategory{SetOb, SetFunction} begin
  dom(f::SetFunction) = f.dom
  codom(f::SetFunction) = f.codom

  id(A::SetOb) = SetFunction(identity, A, A)

  function compose(f::SetFunction, g::SetFunction)
    codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    compose_id(f, g)
  end
end

@inline compose_id(f::SetFunction, g::SetFunction) = compose_inv(f, g)
@inline compose_id(f::SetFunction, ::IdentityFunction) = f
@inline compose_id(::IdentityFunction, g::SetFunction) = g
@inline compose_id(f::IdentityFunction, ::IdentityFunction) = f

# Developer's note: `compose_inv` and its helper `comp_inv_helper` are
# introduced here to ensure that `f` and `inv(f)` will compose to the
# appropriate `IdentityFunction` object when they meet. In this, the type
# `BijectionBimap` plays the decisive role. It provides an effective
# representation of a function whose inverse is known. But note, the same
# behavior is not guaranteed for some instances of `FinBijection`s. That is,
# composition of inverses is not guaranteed to result in an `IdentityFunction`.
# See test/categorical_algebra/FinSets.jl.
#
# The implementation of `compose_inv` is somewhat tortured, and it is due in
# part to a disadvantage of the extant `CompositeFunction` type. Iterated
# composites are represented essentially as a tree of `SetFunction`s. As a
# consequence, it is not possible to tell from the type of a `CompositeFunction`
# whether the leftmost (or rightmost) item of the composite is a
# `BijectionBimap`. Because of all this, the implementation introduces an
# efficiency loss whenever using `compose` with a `CompositeFunction`, which
# grows worse as the "tree" of composites grows deeper. To make things simpler
# for `compose_inv`, the obvious idea would be to try refactoring
# `CompositeFunction` to store a list of `SetFunction`s instead of a pair.

function compose_inv(f::SetFunction, g::SetFunction)
  delved = comp_inv_helper(f, g) # the helper "delves" into composites
  if delved !== nothing; delved else do_compose(f, g) end
end

comp_inv_helper(f::SetFunction, g::SetFunction) = nothing
function comp_inv_helper(f::SetFunction, g::Composite)
  delved = comp_inv_helper(f, first(g))
  if delved === nothing; nothing
  elseif delved isa IdentityFunction; last(g)
  else do_compose(delved, last(g)) end
end
function comp_inv_helper(f::Composite, g::SetFunction)
  delved = comp_inv_helper(last(f), g)
  if delved === nothing; nothing
  elseif delved isa IdentityFunction; first(f)
  else do_compose(first(f), delved) end
end
function comp_inv_helper(f::Composite, g::Composite)
  delved = comp_inv_helper(last(f), first(g))
  if delved === nothing; nothing
  elseif delved isa IdentityFunction; compose_inv(first(f), last(g)) # `compose_inv` here instead of `do_compose`
  else do_compose(do_compose(first(f), delved), last(g)) end
end
function comp_inv_helper(f::F, g::BijectionBimap{X, Y, Z, Inv}) where
    {X, Y, Z, Dom<:SetOb, Codom<:SetOb, Inv<:SetFunction{Dom,Codom},
    F<:Union{Inv, AbsBijectionWrapper{Dom,Codom,Inv}}}
  if unwrap(f) === g.inv; id(dom(f)) else nothing end
end
function comp_inv_helper(f::BijectionBimap{X, Y, Z, Inv}, g::G) where
    {X, Y, Z, Dom<:SetOb, Codom<:SetOb, Inv<:SetFunction{Dom,Codom},
    G<:Union{Inv, AbsBijectionWrapper{Dom,Codom,Inv}}}
  if f.inv === unwrap(g); id(dom(f)) else nothing end
end
function comp_inv_helper(f::BijectionBimap{W, X, F, G},
    g::BijectionBimap{Y,Z,G,F}) where {W,X,Y,Z,F<:SetFunction,G<:SetFunction}
  if f.func === g.inv || f.inv === g.func; id(dom(f)) else nothing end
end

do_compose(f::SetFunction, g::SetFunction) = Composite(f, g)
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

universal(lim::Terminal{TypeSet{Nothing}}, span::SMultispan{0}) =
  ConstantFunction(nothing, apex(span), ob(lim))

limit(Xs::SingletonDiagram{<:TypeSet}) = limit(Xs, SpecializeLimit())

function limit(Xs::ObjectPair{<:TypeSet})
  X1, X2 = Xs
  X = TypeSet(Tuple{eltype(X1),eltype(X2)})
  π1, π2 = SetFunction(first, X, X1), SetFunction(last, X, X2)
  Limit(Xs, Span(π1, π2))
end

function universal(lim::BinaryProduct{<:TypeSet}, span::Span)
  f, g = span
  SetFunction(x -> (f(x),g(x)), apex(span), ob(lim))
end

function limit(Xs::DiscreteDiagram{<:TypeSet})
  X = TypeSet(Tuple{map(eltype, Xs)...})
  πs = [ SetFunction(x -> getindex(x, i), X, Xi) for (i, Xi) in enumerate(Xs) ]
  Limit(Xs, Multispan(X, πs))
end

function universal(lim::Product{<:TypeSet}, span::Multispan)
  @assert length(cone(lim)) == length(span)
  fs = Tuple(legs(span))
  SetFunction(x -> map(f -> f(x), fs), apex(span), ob(lim))
end

function limit(cospan::Multicospan{<:TypeSet})
  eltype(apex(cospan)) == Nothing ? product(feet(cospan)) :
    error("Pullbacks of TypeSets that are not products are not supported")
end

# Colimits
##########

colimit(Xs::SingletonDiagram{<:TypeSet}) = colimit(Xs, SpecializeColimit())

end
