""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredMulticospan, StructuredCospan, StructuredCospanOb,
  OpenCSetTypes, OpenACSetTypes, OpenACSetLeg

using StructEquality
using StaticArrays: StaticVector, SVector

using ACSets, GATlab

using ....Theories: ThCategory
import ....Theories: dom, codom, compose, ⋅, id, otimes, ⊗, munit, braid, σ, 
  mcopy, Δ, mmerge, ∇, delete, ◊, create, □, dunit, dcounit, dagger


using ....BasicSets, ...Cats, ...SetCats
import ....BasicSets: ≃  
import ...Cats: apex, legs, feet, left, right, bundle_legs, components, force
using ..Pointwise 

# Generic structured cospans
############################

""" Structured multicospan.

A structured multicospan is like a structured cospan except that it may have a
number of legs different than two.

See also: [`StructuredCospan`](@ref).
"""
@struct_hash_equal struct StructuredMulticospan{L, Cosp <: Multicospan,
                                               Feet <: AbstractVector}
  cospan::Cosp
  feet::Feet

  """ Construct structured multicospan in L-form.
  """
  StructuredMulticospan{L}(cospan::Cosp, feet::Feet) where
      {L, Cosp <: Multicospan, Feet <: AbstractVector} =
    new{L,Cosp,Feet}(cospan, feet)
end

function ≃(a::StructuredMulticospan, b::StructuredMulticospan)
  a.feet == b.feet || return false
  length(a.cospan) == length(b.cospan) || return false
  all(((x,y),)-> x ≃ y, zip(a.cospan, b.cospan))
end

""" Construct structured multicospan in R-form.
"""
function StructuredMulticospan{L}(x, cospan::Multicospan) where L
  StructuredMulticospan{L}(
    Multicospan(x, map(leg -> shift_left(L, x, leg), legs(cospan))),
    dom.(legs(cospan)))
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

function bundle_legs(cospan::StructuredMulticospan{L}, indices) where L
  cat = infer_acset_cat(apex(cospan))
  m, postprocess = if first(feet(cospan)) isa FinSet 
    SkelFinSet(), FinSet 
  else 
    infer_acset_cat(first(feet(cospan))), identity 
  end
  StructuredMulticospan{L}(bundle_legs(cospan.cospan, indices, cat),
                           map(i -> postprocess(bundle_feet(cospan, i, m)), indices))
end

bundle_feet(cospan, i::Int, m) = feet(cospan)[i]
bundle_feet(cospan, i::Tuple, m) = bundle_feet(cospan, SVector(i), m)
function bundle_feet(cospan, i::AbstractVector{Int}, m) 
  ob(coproduct[m](feet(cospan)[i]...))
end

# Hypergraph category of structured cospans
###########################################

""" Object in the category of L-structured cospans.
"""
@struct_hash_equal struct StructuredCospanOb{L,T}
  ob::T
  StructuredCospanOb{L}(ob::T) where {L,T} = new{L,T}(ob)
end

function StructuredCospan{L}(cospan::Cospan, lfoot::StructuredCospanOb{L},
                             rfoot::StructuredCospanOb{L}) where L
  StructuredCospan{L}(cospan, SVector(lfoot.ob, rfoot.ob))
end

# FIXME: Instances don't support type parameters.
# @instance ThHypergraphCategory{StructuredCospanOb{L}, StructuredCospan{L}} where L begin
begin
  dom(cospan::StructuredCospan{L}) where L =
    StructuredCospanOb{L}(first(feet(cospan)))
  codom(cospan::StructuredCospan{L}) where L =
    StructuredCospanOb{L}(last(feet(cospan)))

  function id(a::StructuredCospanOb{L,T}) where {L,T} 
    x = L(a.ob)
    i = id[infer_acset_cat(x)](x)
    StructuredCospan{L}(Cospan(x, i, i), a, a)
  end

  function compose(M::StructuredCospan{L}, N::StructuredCospan{L}) where L
    @withmodel infer_acset_cat(apex(M)) (pushout, ⋅, ob) begin 
      ιM, ιN = colim = pushout(right(M), left(N))
      cospan = Cospan(ob(colim), left(M)⋅ιM, right(N)⋅ιN)
      StructuredCospan{L}(cospan, dom(M), codom(N))
    end
  end

  otimes(a::StructuredCospanOb{L}, b::StructuredCospanOb{L}) where L =
    if a.ob isa FinSet 
      StructuredCospanOb{L}(FinSet(ob(coproduct[SkelFinSet()](a.ob, b.ob))))
    else 
      StructuredCospanOb{L}(ob(coproduct[infer_acset_cat(a.ob)](a.ob, b.ob)))
    end
      

  function otimes(M::StructuredCospan{L}, N::StructuredCospan{L}) where L
    𝒞 = infer_acset_cat(apex(M));
    @withmodel 𝒞 (coproduct, copair,⋅) begin 
      ιM, ιN = colim = coproduct(apex(M), apex(N))
      cospan = Cospan(ob(colim),
        copair(coproduct(dom(left(M)), dom(left(N))), left(M)⋅ιM, left(N)⋅ιN),
        copair(coproduct(dom(right(M)), dom(right(N))), right(M)⋅ιM, right(N)⋅ιN))
      StructuredCospan{L}(cospan, dom(M)⊗dom(N), codom(M)⊗codom(N))
  end
  end

  munit(::Type{StructuredCospanOb{L}}) where L =
    StructuredCospanOb{L}(FinSet(0)) # do this for real once we use models

  function braid(a::StructuredCospanOb{L}, b::StructuredCospanOb{L}) where L
    x, y = L(a.ob), L(b.ob)
    𝒞 = infer_acset_cat(x)
    xy, yx = coproduct[𝒞](x, y), coproduct[𝒞](y, x)
    cospan = Cospan(ob[𝒞](xy), id[𝒞](ob(xy)), copair[𝒞](yx, coproj2(xy), coproj1(xy)))
    StructuredCospan{L}(cospan, a⊗b, b⊗a)
  end

  function mcopy(a::StructuredCospanOb{L}) where L  
    x = L(a.ob)
    𝒞 = infer_acset_cat(x)
    CM = TypedCatWithCoproducts(𝒞)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, i, copair[CM](i,i)), a, a⊗a)
  end

  function mmerge(a::StructuredCospanOb{L}) where L  
    x = L(a.ob)
    𝒞 = infer_acset_cat(x)
    CM = TypedCatWithCoproducts(𝒞)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, copair[CM](i,i), i), a⊗a, a)
  end

  function delete(a::StructuredCospanOb{L}) where L  
    x = L(a.ob) 
    𝒞 = infer_acset_cat(x)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, i, create[𝒞](x)), a, munit_like(a))
  end

  function create(a::StructuredCospanOb{L}) where L 
    x = L(a.ob)
    𝒞 = infer_acset_cat(x)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, create[𝒞](x), i), munit_like(a), a)
  end

  function dunit(a::StructuredCospanOb{L}) where L  
    x = L(a.ob)
    𝒞 = infer_acset_cat(x)
    CM = TypedCatWithCoproducts(𝒞)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, create[𝒞](x), copair[CM](i,i)), munit_like(a), a⊗a)
  end

  function dcounit(a::StructuredCospanOb{L}) where L 
    x = L(a.ob)
    𝒞 = infer_acset_cat(x)
    CM = TypedCatWithCoproducts(𝒞)
    i = id[𝒞](x)
    StructuredCospan{L}(Cospan(x, copair[CM](i,i), create[𝒞](x)), a⊗a, munit_like(a))
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

A special case of [`OpenACSetTypes`](@ref). See there for details.
"""
function OpenCSetTypes(::Type{X}, args...) where X<:StructCSet
  OpenACSetTypes(X, args...)
end

""" Create types for open attributed C-sets from an attributed C-set type.

The type parameters of the given acset type should *not* be instantiated with
specific Julia types. This function returns a pair of types, one for objects, a
subtype of [`StructuredCospanOb`](@ref), and one for morphisms, a subtype of
[`StructuredMulticospan`](@ref). Both types will have the same type parameters
for attribute types as the given acset type.

Mathematically speaking, this function sets up structured (multi)cospans with a
functor ``L: A → X`` between categories of acsets that creates "discrete
acsets." Such a "discrete acset functor" is a functor that is left adjoint to a
certain kind of forgetful functor between categories of acsets, namely one that
is a pullback along an inclusion of schemas such that the image of inclusion has
no outgoing arrows. For example, the schema inclusion ``{V} ↪ {E ⇉ V}`` has this
property but ``{E} ↪ {E ⇉ V}`` does not.

See also: [`OpenCSetTypes`](@ref).
"""
function OpenACSetTypes(::Type{X}, ob₀::Symbol) where {S, X<:StructACSet{S}}
  @assert ob₀ ∈ ob(S)
  vars = map(TypeVar, attrtypes(S))
  L = if any(d == ob₀ for (_,d,_) in attrs(S))
    A = ACSetTableType(X, ob₀, union_all=true)
    DiscreteACSet{A{vars...}, X{vars...}}
  else
    FinSetDiscreteACSet{ob₀, isempty(vars) ? X : X{vars...}}
  end
  (foldr(UnionAll, vars, init=StructuredCospanOb{L}),
   foldr(UnionAll, vars, init=StructuredMulticospan{L}))
end

function OpenACSetTypes(::Type{X}, ::Type{A}) where
    {S, X<:StructACSet{S}, S₀, A<:StructACSet{S₀}}
  @assert ob(S₀) ⊆ ob(S) && hom(S₀) ⊆ hom(S) && attr(S₀) ⊆ attr(S)
  attr_types₀, attr_types = collect(attrtype(S₀)), collect(attrtype(S))
  attr_type_indices₀ = indexin(attr_types₀, attr_types)
  @assert all(!isnothing, attr_type_indices₀)

  vars = map(TypeVar, attrtype(S))
  vars₀ = vars[attr_type_indices₀]
  L = isempty(vars) ? DiscreteACSet{A,X} : DiscreteACSet{A{vars₀...}, X{vars...}}
  (foldr(UnionAll, vars, init=StructuredCospanOb{L}),
   foldr(UnionAll, vars, init=StructuredMulticospan{L}))
end

""" Leg of a structured (multi)cospan of acsets in R-form.

A convenience type that contains the data of an acset transformation, except for
the codomain, since that data is already given by the decoration of the R-form
structured cospan.
"""
@struct_hash_equal struct OpenACSetLeg{Comp<:NamedTuple, Dom<:StructACSet}
  components::Comp
  dom::Dom
end
OpenACSetLeg(a::StructACSet; components...) = OpenACSetLeg((; components...), a)

components(ϕ::OpenACSetLeg) = ϕ.components
dom(ϕ::OpenACSetLeg) = ϕ.dom

# This has been changed from `nothing`. It needs to be a fixed value in order 
# for cospans to compose (attribute values may mismatch) but without really 
# doing things right with models, we want the type to be the same as the dom 
# type (given that (Co)Spans don't really know how to get their feet without 
# providing a ThCategory model).
codom(ϕ::OpenACSetLeg) = typeof(ϕ.dom)()  

""" Abstract type for functor L: A → X giving a discrete attribute C-set.
"""
abstract type AbstractDiscreteACSet{X <: StructACSet} end

codom(::Type{<:AbstractDiscreteACSet{X}}) where
  {S, X<:StructACSet{S}} = (X, StructACSetTransformation{S})

StructuredCospan{L}(x::StructACSet, f::Union{FinFunction,OpenACSetLeg},
                    g::Union{FinFunction,ACSetTransformation}) where
    {L<:AbstractDiscreteACSet} =
  StructuredCospan{L}(x, Cospan(f, g))

function StructuredMulticospan{L}(x::StructACSet,
                         fs::Vararg{Union{FinFunction,OpenACSetLeg},N}; cat=nothing) where
    {L<:AbstractDiscreteACSet, N}
  StructuredMulticospan{L}(x, SMulticospan{N}(fs...))
end

function force(M::StructuredMulticospan{L}) where {L<:AbstractDiscreteACSet}
  StructuredMulticospan{L}(
    Multicospan(apex(M.cospan), map(force, legs(M.cospan))), M.feet)
end

""" A functor L: FinSet → C-Set giving the discrete C-set wrt an object in C.

This functor has a right adjoint R: C-Set → FinSet giving the underlying set at
that object.
"""
struct FinSetDiscreteACSet{ob₀, X} <: AbstractDiscreteACSet{X} end

dom(::Type{<:FinSetDiscreteACSet}) = (FinSet, FinFunction)

""" A functor L: C₀-Set → C-Set giving the discrete C-set for C₀.

Unlike [`FinSetDiscreteACSet`](@ref), this type supports data attributes. In
addition, the sub-schema C₀ may contain more than one object. In all cases, the
inclusion of schemas ``C₀ → C`` must satisfy the property described in
[`OpenACSetTypes`](@ref).
"""
struct DiscreteACSet{A <: StructACSet, X} <: AbstractDiscreteACSet{X} end

dom(::Type{<:DiscreteACSet{A}}) where {S, A<:StructACSet{S}} =
  (A, StructACSetTransformation{S})

function StructuredMulticospan{L}(x::StructACSet,
                                  cospan::Multicospan{<:FinSet}; cat=nothing) where
    {A, L <: DiscreteACSet{A}}
  a = A()
  copy_parts!(a, x)
  induced_legs = map(leg -> induced_transformation(a, leg), legs(cospan))
  StructuredMulticospan{L}(x, Multicospan(a, induced_legs))
end

function StructuredCospanOb{L}(set::FinSet; kw...) where
    {S, A <: StructACSet{S}, L <: DiscreteACSet{A}}
  a = A()
  add_parts!(a, only(ob(S)), length(set); kw...)
  StructuredCospanOb{L}(a)
end

""" C-set transformation b → a induced by function `f` into parts of `a`.
"""
function induced_transformation(a::A, f::FinFunction) where
    {S, A <: StructACSet{S}}
  ob₀ = only(ob(S))
  @assert nparts(a, ob₀) == length(codom(f))
  b = A()
  add_parts!(b, ob₀, length(dom(f)))
  f_vec = collect(f)
  for attr in attr(S)
    set_subpart!(b, attr, subpart(a, f_vec, attr))
  end
  cat = infer_acset_cat(a)
  ACSetTransformation((; ob₀ => f), b, a; cat)
end

""" Apply left adjoint L: FinSet → C-Set to object.
"""
function (::Type{L})(a::FinSet) where {ob₀,X,L<:FinSetDiscreteACSet{ob₀,X}}
  x = X()
  add_parts!(x, ob₀, length(a))
  x
end

""" Apply left adjoint L: C₀-Set → C-Set to object.
"""
function (::Type{L})(a::StructACSet) where {A,X,L<:DiscreteACSet{A,X}}
  x = X()
  copy_parts!(x, a)
  x
end

""" Apply left adjoint L: FinSet → C-Set to morphism.
"""
function (::Type{L})(f::FinFunction) where
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
function shift_left(::Type{L}, x::StructACSet, f::FinFunction) where
    {ob₀, L <: FinSetDiscreteACSet{ob₀}}
  ACSetTransformation((; ob₀ => f), L(dom(f)), x; cat=infer_acset_cat(x))
end
function shift_left(::Type{L}, x::StructACSet,
                    ϕ::Union{ACSetTransformation,OpenACSetLeg}) where
    {L <: DiscreteACSet}
  ACSetTransformation(components(ϕ), L(dom(ϕ)), x)
end

end
