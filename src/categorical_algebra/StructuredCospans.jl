""" Structured cospans.

This module provides a generic interface for structured cospans with a concrete
implementation for attributed C-sets.
"""
module StructuredCospans
export StructuredMulticospan, StructuredCospan, StructuredCospanOb,
  OpenCSetTypes, OpenACSetTypes, StructuredMultiCospanHom,
  openrule, idH_, idV_, composeV_, composeH_, id2_, id2V_, id2H_,
  open_homomorphisms, can_open_pushout_complement

using AutoHashEquals
using StaticArrays: StaticVector, SVector

using ...GAT, ..FreeDiagrams, ..Limits, ..FinSets, ..CSets, ...Present, ...Theories
import ..FreeDiagrams: apex, legs, feet, left, right, bundle_legs
import ..CSets: force
import ...CSetDataStructures: struct_acset
using ...Theories: Category, SchemaDesc, SchemaDescType, CSetSchemaDescType, SchemaDescTypeType,
  attrtype, attr, adom, adom_nums, acodom, dom, codom
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

# Maps between structured multicospans
######################################
"""
A component-wise map between two cospans. The first component given is the apex
map, with the following maps being the legs.
"""
struct StructuredMultiCospanHom{L}
  src::StructuredMulticospan{L}
  tgt::StructuredMulticospan{L}
  maps::Vector{<:ACSetTransformation} # one for each leg, plus apex
  function StructuredMultiCospanHom(s::StructuredMulticospan{L},
    t::StructuredMulticospan{L}, m::Vector{<:ACSetTransformation}) where {L}
    length(m) == length(legs(s)) + 1 || error("bad # maps")
    length(m) == length(legs(t)) + 1 || error("bad # maps")

    for (i,(s_leg, t_leg, st_map)) in enumerate(zip(legs(s), legs(t), m[2:end]))
      ms, mt = force(s_leg ⋅ m[1]), force(st_map ⋅ t_leg)
      dom(ms) == dom(mt) || error("domain error $(dom(ms)) $(dom(mt))")
      codom(ms) == codom(mt) || error("codomain error $(codom(ms)) $(codom(mt))")
      ms == mt || error(
        "diagram $i does not commute")
      force(st_map) ∈ isomorphisms(dom(st_map), codom(st_map)) || error(
        "leg map $i is not iso: $st_map")
      is_natural(s_leg)  || error("src leg $i not natural")
      is_natural(t_leg)  || error("tgt leg $i not natural")
      is_natural(st_map) || error("st_map  $i not natural")

    end
    return new{L}(s,t,m)
  end
end

dom(x::StructuredMultiCospanHom) = x.src
codom(x::StructuredMultiCospanHom) = x.tgt

"""
Find homomorphisms between structured cospans. These are constrained to be iso
on the legs of the cospans. Solving this w/ homomorphism finding  requires a
dynamic acset, and the current hack will be replaced once those are available.
"""
function open_homomorphisms(pat::StructuredMulticospan{L},
                            tgt::StructuredMulticospan{L};
                            monic::Bool=false
                           )::Vector{StructuredMultiCospanHom{L}} where L
  # make modified ACSet that includes cospan info
  #----------------------------------------------
  V = L.parameters[1]
  p = Presentation(L.parameters[2]())
  Ls, ls = Symbol[], Symbol[]
  for i in 1:length(legs(pat))
    Leg, leg = Symbol("_Leg_$i"), Symbol("_leg_$i")
    push!(ls, leg)
    push!(Ls, Leg)
    add_generator!(p, Ob(FreeSchema, Leg))
    add_generator!(p, Hom(leg, p[Leg], p[V]))
  end
  name = Symbol("open_$(L.parameters[2].name.name)")
  t = struct_acset(name, StructACSet, p, index=ls)
  try
    eval(t)
  catch e
    e isa ErrorException && e.msg[1:20] == "invalid redefinition" || throw(e)
  end
  # Copy old ACSet info from homomorphism source and target
  #--------------------------------------------------------
  tpat, ttgt = [Base.invokelatest(eval(name)) for _ in 1:2]
  copy_parts!(tpat, apex(pat))
  copy_parts!(ttgt, apex(tgt))

  # Add leg data data to each ACset
  #--------------------------------
  for (Lname, lname, l) in zip(Ls, ls, legs(pat))
    add_parts!(tpat, Lname, nparts(dom(l), V); Dict([lname => collect(l[V])])...)
  end
  for (Lname, lname, l) in zip(Ls, ls, legs(tgt))
    add_parts!(ttgt, Lname, nparts(dom(l), V); Dict([lname => collect(l[V])])...)
  end

  # Compute homomorphisms in alternate schema
  #------------------------------------------
  matches = homomorphisms(tpat, ttgt, monic=monic, iso=Ls)

  # Process homomorphism finding results
  #-------------------------------------
  res = [StructuredMultiCospanHom(pat, tgt,
    [ACSetTransformation(apex(pat), apex(tgt);
                         Dict([k=>v for (k, v) in pairs(mtch.components)
                               if !(k in Ls)])...), # first map, on apexes
      [L(mtch[l]) for l in Ls]...]) # remaining maps, for each leg
    for mtch in matches]
  return res
end


function can_open_pushout_complement(f::StructuredMultiCospanHom{L},
                                     g::StructuredMultiCospanHom{L}
                                     )::Bool where L
  all([can_pushout_complement(ComposablePair(a,b))
       for (a,b) in zip(f.maps, g.maps)])
end

"""A span of StructuredMulticospanHoms, interpreted as a DPO rewrite rule"""
struct openrule
  data::Span # Intended to be span of StructuredMulticospanHoms
end

# Functions for the double category of structured multicospan rewrites
#---------------------------------------------------------------------
# Objects are finite sets (StructuredCospanOb{L})
# Horizontal arrows are structured multicospans
# Vertical arrows are spans of invertible finfunctions

function idH_(a::StructuredCospanOb{L}) where {L}
  x = L(FinSet(a.ob))
  i = id(x)
  return StructuredCospan{L}(Cospan(x, i, i), a, a)
end

"""Vertical arrows are spans of invertible finfunctions"""
function idV_(a::StructuredCospanOb{L}) where {L}
  x = L(FinSet(a.ob))
  i = id(x)
  return Span(i, i)
end

"""Cospan composition given by pushout"""
function composeH_(f::StructuredCospan{L}, g::StructuredCospan{L})::StructuredCospan{L} where {L}
  return compose(f,g)
end

"""Finset span composition given by pullback"""
function composeV_(f::Span, g::Span)::Span where {T}
  pbf, pbg = pullback(right(f), left(g))
  return Span(compose(pbf, left(f)), compose(pbg,right(g)))
end

function id2_(A::StructuredCospanOb{L})::openrule where {L}
  i = idH_(A)
  v = left(idV_(A))
  m = StructuredMultiCospanHom(i,i,[v,v,v])
  return openrule(Span(m,m))
end

"""
Pass dummy value in because a span of invertible FinFunctions does not retain
L type
"""
function id2H_(f::Span,_::StructuredCospanOb{L_})::openrule where {L_}
  Ll, Lr = L_.(f)
  sc     = idH_(StructuredCospanOb{L_}(dom(left(f))))
  up     = StructuredMultiCospanHom(sc, sc, [Ll, Ll, Ll])
  down   = StructuredMultiCospanHom(sc, sc, [Lr, Lr, Lr])
  return openrule(Span(up, down))
end

function id2V_(f::StructuredMulticospan{L})::openrule where {L}
  m = StructuredMultiCospanHom(f, f,
        vcat([id(apex(f))], [id(dom(x)) for x in legs(f)]))
  return openrule(Span(m,m))
end

"""    composeH_(r₁, r₂)
compose two rewrite rules horizontally (via pushouts) as shown below:

    L₁₋₍ₙ₋₁₎-> L <- Lₙ    X₁ -> X <- X₂₋ₘ     L₁₋₍ₙ₋₁₎ -> L +Lₙ X <- X₂₋ₘ
    ↑        λ ↑    ↑     ↑    ↑ χ    ↑          ↑           ↑        ↑
    I₁₋₍ₙ₋₁₎-> I <- Iₙ ∘h Y₁ -> Y <- Y₂₋ₘ  =  I₁₋₍ₙ₋₁₎ -> I +Iₙ Y <- Y₂₋ₘ
    ↓        ρ ↓    ↓     ↓    ↓ ζ    ↓          ↓           ↓        ↓
    R₁₋₍ₙ₋₁₎-> R <- Rₙ    Z₁ -> Z <- Z₂₋ₘ     R₁₋₍ₙ₋₁₎ -> R +Rₙ Z <- Z₂₋ₘ
 """
function composeH_(f::openrule, g::openrule)::openrule
  λ, ρ = f.data;
  χ, ζ = g.data;
  force(λ.maps[end]) == force(χ.maps[2]) || error("cannot horizontally compose")
  force(ρ.maps[end]) == force(ζ.maps[2]) || error("cannot horizontally compose")
  λapex, ρapex, χapex, ζapex = [m.maps[1] for m in [λ, ρ, χ, ζ]]
  IY = compose(dom(λ), dom(χ));
  LX = compose(codom(λ), codom(χ));
  RZ = compose(codom(ρ), codom(ζ));
  IY_pushout, LX_pushout, RZ_pushout = [
    pushout(legs(left_cospan)[end],legs(right_cospan)[1])
     for (left_cospan,right_cospan) in
     [λ.src => χ.src, λ.tgt => χ.tgt,  ρ.tgt => ζ.tgt]];

  # Universal property, mapping out of a coproduct (into another coproduct)
  IY_LX = universal(IY_pushout, Cospan(compose(λapex, legs(LX_pushout)[1]),
                                       compose(χapex, legs(LX_pushout)[2])));
  IY_RZ = universal(IY_pushout, Cospan(compose(ρapex, legs(RZ_pushout)[1]),
                                       compose(ζapex, legs(RZ_pushout)[2])));
  IY_LX_maps = vcat([IY_LX], λ.maps[2:end-1], χ.maps[3:end])
  IY_RZ_maps = vcat([IY_RZ], ρ.maps[2:end-1], ζ.maps[3:end])
  IL = StructuredMultiCospanHom(IY, LX, IY_LX_maps);
  IR = StructuredMultiCospanHom(IY, RZ, IY_RZ_maps);
  return openrule(Span(IL, IR))
end


"""    composeV_(r₁, r₂)
compose two rewrite rules vertically with pullbacks, as shown below:

       L₁₋ₙ -> L
       ↑       ↑
       I₁₋ₙ -> I
       ↓       ↓         L₁₋ₙ        ->   L
       R₁₋ₙ -> R           ↑              ↑
           ∘v      = I₁₋ₙ ×ᵣ₁₋ₙ  Θ₁₋ₙ -> I ×ᵣ Θ
       Λ₁₋ₙ -> Λ           ↓              ↓
       ↑       ↑         Ω₁₋ₙ        ->   Ω
       Θ₁₋ₙ -> Θ
       ↓       ↓
       Ω₁₋ₙ -> Ω
"""
function composeV_(f_::openrule, g_::openrule)
  (lf, rf), (lg, rg) = (f, g) = f_.data, g_.data;
  L = typeof(left(f)).parameters[1];
  V= L.parameters[1]
  force(left(g).tgt) == force(right(f).tgt) || error("cannot compose $f and $g")
  pbs = [pullback(rf,lg) for (rf,lg) in zip(right(f).maps, left(g).maps)];
  upmaps = [compose(legs(pb)[1], lfm) for (pb, lfm) in zip(pbs, lf.maps)];
  dnmaps = [compose(legs(pb)[2], rgm) for (pb, rgm) in zip(pbs, rg.maps)];
  Imaps  = [compose(legs(pb)[1], im) for (pb, im) in zip(pbs[2:end], legs(lf.src))];
  Θmaps  = [compose(legs(pb)[2], θm) for (pb, θm) in zip(pbs[2:end], legs(rg.src))];
  xmaps  = [universal(pbs[1], Span(im, θm)) for (im, θm) in zip(Imaps, Θmaps)];
  newcenter = StructuredMulticospan{L}(
    apex(pbs[1]), Multicospan([xm[V] for xm in xmaps]));
  newl = StructuredMultiCospanHom(newcenter, lf.tgt, upmaps);
  newr = StructuredMultiCospanHom(newcenter, rg.tgt, dnmaps);
  return openrule(Span(newl, newr))
end


end
