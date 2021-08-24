""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredMulticospan, StructuredCospan, StructuredCospanOb,
  OpenCSetTypes, OpenACSetTypes

using AutoHashEquals
using StaticArrays: StaticVector, SVector

using ...GAT, ..FreeDiagrams, ..Limits, ..FinSets, ..CSets
import ..FreeDiagrams: apex, legs, feet, left, right, bundle_legs
import ..CSets: force
using ...Theories: Category, SchemaDesc, SchemaDescType, CSetSchemaDescType, SchemaDescTypeType,
  attrtype, attr, adom, adom_nums, acodom
import ...Theories: dom, codom, compose, ⋅, id, otimes, ⊗, munit, braid, σ,
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □, dunit, dcounit, dagger

# Generic structured cospans
############################

""" Structured multicospan.

A structured multicospan is like a structured cospan except that it may have a
number of legs different than two.

See also: [`StructuredCospan`](@ref).
"""
@auto_hash_equals struct StructuredMulticospan{L, Cosp <: Multicospan,
                                               Feet <: AbstractVector}
  cospan::Cosp
  feet::Feet

  """ Construct structured multicospan in L-form.
  """
  StructuredMulticospan{L}(cospan::Cosp, feet::Feet) where
      {L, Cosp <: Multicospan, Feet <: AbstractVector} =
    new{L,Cosp,Feet}(cospan, feet)
end

""" Construct structured multicospan in R-form.
"""
function StructuredMulticospan{L}(x, cospan::Multicospan) where L
  StructuredMulticospan{L}(
    Multicospan(x, map(leg -> shift_left(L, x, leg), legs(cospan))),
    feet(cospan))
end

apex(cospan::StructuredMulticospan) = apex(cospan.cospan)
legs(cospan::StructuredMulticospan) = legs(cospan.cospan)
feet(cospan::StructuredMulticospan) = cospan.feet

""" Structured cospan.

The first type parameter `L` encodes a functor L: A → X from the base category
`A`, often FinSet, to a category `X` with "extra structure." An L-structured
cospan is then a cospan in X whose feet are images under L of objects in A. The
category X is assumed to have pushouts.

Structured cospans form a double category with no further assumptions on the
functor L. To obtain a symmetric monoidal double category, L must preserve
finite coproducts. In practice, L usually has a right adjoint R: X → A, which
implies that L preserves all finite colimits. It also allows structured cospans
to be constructed more conveniently from an object x in X plus a cospan in A
with apex R(x).

See also: [`StructuredMulticospan`](@ref).
"""
const StructuredCospan{L, Cosp <: Cospan, Feet <: StaticVector{2}} =
  StructuredMulticospan{L,Cosp,Feet}

""" Construct structured cospan in L-form.
"""
StructuredCospan{L}(cospan::Cospan, feet::StaticVector{2}) where L =
  StructuredMulticospan{L}(cospan, feet)

""" Construct structured cospan in R-form.
"""
StructuredCospan{L}(apex, cospan::Cospan) where L =
  StructuredMulticospan{L}(apex, cospan)

left(cospan::StructuredCospan) = first(legs(cospan))
right(cospan::StructuredCospan) = last(legs(cospan))

bundle_legs(cospan::StructuredMulticospan{L}, indices) where L =
  StructuredMulticospan{L}(bundle_legs(cospan.cospan, indices),
                           map(i -> bundle_feet(cospan, i), indices))

bundle_feet(cospan, i::Int) = feet(cospan)[i]
bundle_feet(cospan, i::Tuple) = bundle_feet(cospan, SVector(i))
bundle_feet(cospan, i::AbstractVector{Int}) = ob(coproduct(feet(cospan)[i]))

# Hypergraph category of structured cospans
###########################################

""" Object in the category of L-structured cospans.
"""
@auto_hash_equals struct StructuredCospanOb{L,T}
  ob::T
  StructuredCospanOb{L}(ob::T) where {L,T} = new{L,T}(ob)
end

function StructuredCospan{L}(cospan::Cospan, lfoot::StructuredCospanOb{L},
                             rfoot::StructuredCospanOb{L}) where L
  StructuredCospan{L}(cospan, SVector(lfoot.ob, rfoot.ob))
end

# FIXME: Instances don't support type parameters.
# @instance HypergraphCategory{StructuredCospanOb{L}, StructuredCospan{L}} where L begin
begin
  dom(cospan::StructuredCospan{L}) where L =
    StructuredCospanOb{L}(first(feet(cospan)))
  codom(cospan::StructuredCospan{L}) where L =
    StructuredCospanOb{L}(last(feet(cospan)))

  id(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, i, i), a, a)
  end

  function compose(M::StructuredCospan{L}, N::StructuredCospan{L}) where L
    ιM, ιN = colim = pushout(right(M), left(N))
    cospan = Cospan(ob(colim), left(M)⋅ιM, right(N)⋅ιN)
    StructuredCospan{L}(cospan, dom(M), codom(N))
  end

  otimes(a::StructuredCospanOb{L}, b::StructuredCospanOb{L}) where L =
    StructuredCospanOb{L}(ob(coproduct(a.ob, b.ob)))

  function otimes(M::StructuredCospan{L}, N::StructuredCospan{L}) where L
    ιM, ιN = colim = coproduct(apex(M), apex(N))
    cospan = Cospan(ob(colim),
      copair(coproduct(dom(left(M)), dom(left(N))), left(M)⋅ιM, left(N)⋅ιN),
      copair(coproduct(dom(right(M)), dom(right(N))), right(M)⋅ιM, right(N)⋅ιN))
    StructuredCospan{L}(cospan, dom(M)⊗dom(N), codom(M)⊗codom(N))
  end

  munit(::Type{StructuredCospanOb{L}}) where L =
    StructuredCospanOb{L}(ob(initial(first(dom(L)))))

  function braid(a::StructuredCospanOb{L}, b::StructuredCospanOb{L}) where L
    x, y = L(a.ob), L(b.ob)
    xy, yx = coproduct(x, y), coproduct(y, x)
    cospan = Cospan(ob(xy), id(ob(xy)), copair(yx, coproj2(xy), coproj1(xy)))
    StructuredCospan{L}(cospan, a⊗b, b⊗a)
  end

  mcopy(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, i, copair(i,i)), a, a⊗a)
  end
  mmerge(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, copair(i,i), i), a⊗a, a)
  end
  delete(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, i, create(x)), a, munit_like(a))
  end
  create(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, create(x), i), munit_like(a), a)
  end

  dunit(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, create(x), copair(i,i)), munit_like(a), a⊗a)
  end
  dcounit(a::StructuredCospanOb{L}) where L = let x = L(a.ob), i = id(x)
    StructuredCospan{L}(Cospan(x, copair(i,i), create(x)), a⊗a, munit_like(a))
  end
  
  dagger(M::StructuredCospan{L}) where L =
    StructuredCospan{L}(Multicospan(apex(M), reverse(legs(M))),
                        reverse(feet(M)))
end

munit_like(a::StructuredCospanOb{L}) where L = munit(StructuredCospanOb{L})

# XXX: Needed because we're not using `@instance`.
⋅(M::StructuredCospan, N::StructuredCospan) = compose(M, N)
⊗(a::StructuredCospanOb, b::StructuredCospanOb) = otimes(a, b)
⊗(M::StructuredCospan, N::StructuredCospan) = otimes(M, N)

# Structured cospans of C-sets
##############################

""" Create types for open C-sets from a C-set type.

Returns two types, for objects, a subtype of [`StructuredCospanOb`](@ref), and
for morphisms, a subtype of [`StructuredMulticospan`](@ref).

See also: [`OpenACSetTypes`](@ref).
"""
function OpenCSetTypes(::Type{X}, ob₀::Symbol) where
    {S<:CSetSchemaDescType, X<:StructCSet{S}}
  @assert ob₀ ∈ ob(S)
  L = FinSetDiscreteACSet{ob₀, X}
  (StructuredCospanOb{L}, StructuredMulticospan{L})
end

""" Create types for open attributed C-sets from an attributed C-set type.

Note: the type passed in should *not* be instantiated with concrete attribute types.

The resulting types, for objects and morphisms, each have the same type
parameters for data types as the original type.

See also: [`OpenCSetTypes`](@ref).
"""
function OpenACSetTypes(::Type{X}, ob₀::Symbol) where
    {S<:SchemaDescType, X<:StructACSet{S}}
  @assert ob₀ ∈ ob(S)
  type_vars = map(TypeVar, attrtype(S))
  L = if any(ob(S)[j] == ob₀ for (i,j) in enumerate(adom_nums(S)))
    A = ACSetTableType(X, ob₀, union_all=true)
    DiscreteACSet{A{type_vars...}, X{type_vars...}}
  else
    FinSetDiscreteACSet{ob₀, X{type_vars...}}
  end
  (foldr(UnionAll, type_vars, init=StructuredCospanOb{L}),
   foldr(UnionAll, type_vars, init=StructuredMulticospan{L}))
end

""" Abstract type for functor L: A → X giving a discrete C-set.
"""
abstract type AbstractDiscreteACSet{X <: StructACSet} end

codom(::Type{<:AbstractDiscreteACSet{X}}) where
  {S, X<:StructACSet{S}} = (X, ACSetTransformation{S})

StructuredCospan{L}(x::StructACSet, f::FinFunction{Int,Int},
                    g::FinFunction{Int,Int}) where {L<:AbstractDiscreteACSet} =
  StructuredCospan{L}(x, Cospan(f, g))

StructuredMulticospan{L}(x::StructACSet,
                         fs::Vararg{<:FinFunction{Int,Int},N}) where
    {L<:AbstractDiscreteACSet, N} =
  StructuredMulticospan{L}(x, SMulticospan{N}(fs...))

function force(M::StructuredMulticospan{L}) where {L<:AbstractDiscreteACSet}
  StructuredMulticospan{L}(
    Multicospan(apex(M.cospan), map(force, legs(M.cospan))), M.feet)
end

""" A functor L: FinSet → C-Set giving the discrete C-set wrt an object in C.

This functor has a right adjoint R: C-Set → FinSet giving the underlying set at
that object. Instead of instantiating this type directly, you should use
[`OpenCSetTypes`](@ref) or [`OpenACSetTypes`](@ref).
"""
struct FinSetDiscreteACSet{ob₀, X} <: AbstractDiscreteACSet{X} end

dom(::Type{<:FinSetDiscreteACSet}) = (FinSet{Int}, FinFunction{Int,Int})

""" A functor L: C₀-Set → C-Set giving the discrete C-set for C₀.

Here C₀ is assumed to contain a single object from C and the discreteness is
with respect to this object. The functor L has a right adjoint R: C-Set → C₀-Set
forgetting the rest of C. Data attributes of the chosen object are preserved.
"""
struct DiscreteACSet{A <: StructACSet, X} <: AbstractDiscreteACSet{X} end

dom(::Type{<:DiscreteACSet{A}}) where {S, A<:StructACSet{S}} =
  (A, ACSetTransformation{S})

function StructuredMulticospan{L}(x::StructACSet,
                                  cospan::Multicospan{<:FinSet{Int}}) where
    {A, L <: DiscreteACSet{A}}
  a = A()
  copy_parts_only!(a, x)
  induced_legs = map(leg -> induced_transformation(a, leg), legs(cospan))
  StructuredMulticospan{L}(x, Multicospan(a, induced_legs))
end

function StructuredCospanOb{L}(set::FinSet{Int}; kw...) where
    {S, A <: StructACSet{S}, L <: DiscreteACSet{A}}
  a = A()
  add_parts!(a, only(ob(S)), length(set); kw...)
  StructuredCospanOb{L}(a)
end

""" C-set transformation b → a induced by function `f` into parts of `a`.
"""
function induced_transformation(a::A, f::FinFunction{Int,Int}) where
    {S, A <: StructACSet{S}}
  ob₀ = only(ob(S))
  @assert nparts(a, ob₀) == length(codom(f))
  b = A()
  add_parts!(b, ob₀, length(dom(f)))
  f_vec = collect(f)
  for attr in attr(S)
    set_subpart!(b, attr, subpart(a, f_vec, attr))
  end
  ACSetTransformation((; ob₀ => f), b, a)
end

""" Apply left adjoint L: FinSet → C-Set to object.
"""
function (::Type{L})(a::FinSet{Int}) where {ob₀,X,L<:FinSetDiscreteACSet{ob₀,X}}
  x = X()
  add_parts!(x, ob₀, length(a))
  x
end

""" Apply left adjoint L: C₀-Set → C-Set to object.
"""
function (::Type{L})(a::StructACSet) where {A,X,L<:DiscreteACSet{A,X}}
  x = X()
  copy_parts_only!(x, a)
  x
end

""" Apply left adjoint L: FinSet → C-Set to morphism.
"""
function (::Type{L})(f::FinFunction{Int,Int}) where
    {ob₀, L <: FinSetDiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f), L(dom(f)), L(codom(f)))
end

""" Apply left adjoint L: C₀-Set → C-Set to morphism.
"""
function (::Type{L})(ϕ::ACSetTransformation) where {L <: DiscreteACSet}
  ACSetTransformation(components(ϕ), L(dom(ϕ)), L(codom(ϕ)))
end

""" Convert morphism a → R(x) to morphism L(a) → x using discrete-forgetful
adjunction L ⊣ R: A ↔ X.
"""
function shift_left(::Type{L}, x::StructACSet, f::FinFunction{Int,Int}) where
    {ob₀, L <: FinSetDiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f), L(dom(f)), x)
end
function shift_left(::Type{L}, x::StructACSet, ϕ::ACSetTransformation) where
    {L <: DiscreteACSet}
  ACSetTransformation(components(ϕ), L(dom(ϕ)), x)
end

end
