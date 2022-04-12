""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  LimitAlgorithm, ColimitAlgorithm,
  ob, cone, cocone, apex, legs, limit, colimit, universal,
  Terminal, Initial, terminal, initial, delete, create, factorize,
  BinaryProduct, Product, product, proj1, proj2, pair,
  BinaryPullback, Pullback, pullback,
  BinaryEqualizer, Equalizer, equalizer, incl,
  BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair,
  BinaryPushout, Pushout, pushout, pushout_complement, can_pushout_complement,
  BinaryCoequalizer, Coequalizer, coequalizer, proj,
  @cartesian_monoidal_instance, @cocartesian_monoidal_instance,
  ComposeProductEqualizer, ComposeCoproductCoequalizer,
  SpecializeLimit, SpecializeColimit, ToBipartiteLimit, ToBipartiteColimit

using AutoHashEquals
using StaticArrays: StaticVector, SVector
using DataStructures: IntDisjointSets, find_root!

using ...GAT, ...Theories, ...Graphs, ...Present
import ...Theories: ob, terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj,
  delete, create, pair, copair, factorize
using ...CSetDataStructures, ..FinCats, ..FreeDiagrams
import ..FreeDiagrams: apex, legs
import ..FinCats: FinCatPresentation

# Data types for limits
#######################

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

ob(lim::AbstractLimit) = apex(lim)
cone(lim::AbstractLimit) = lim.cone
apex(lim::AbstractLimit) = apex(cone(lim))
legs(lim::AbstractLimit) = legs(cone(lim))

Base.iterate(lim::AbstractLimit, args...) = iterate(cone(lim), args...)
Base.eltype(lim::AbstractLimit) = eltype(cone(lim))
Base.length(lim::AbstractLimit) = length(cone(lim))

""" Limit in a category.
"""
@auto_hash_equals struct Limit{Ob,Diagram,Cone<:Multispan{Ob}} <:
    AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
end

const Terminal{Ob} = AbstractLimit{Ob,<:EmptyDiagram}
const BinaryProduct{Ob} = AbstractLimit{Ob,<:ObjectPair}
const Product{Ob} = AbstractLimit{Ob,<:DiscreteDiagram}
const BinaryPullback{Ob} = AbstractLimit{Ob,<:Cospan}
const Pullback{Ob} = AbstractLimit{Ob,<:Multicospan}
const BinaryEqualizer{Ob} = AbstractLimit{Ob,<:ParallelPair}
const Equalizer{Ob} = AbstractLimit{Ob,<:ParallelMorphisms}

proj1(lim::Union{BinaryProduct,BinaryPullback}) = first(legs(lim))
proj2(lim::Union{BinaryProduct,BinaryPullback}) = last(legs(lim))
incl(eq::Equalizer) = only(legs(eq))

""" Algorithm for computing limits.
"""
abstract type LimitAlgorithm end

# Data types for colimits
#########################

""" Abstract type for colimit in a category.

The standard concrete subtype is [`Colimit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractColimit{Ob,Diagram} end

ob(colim::AbstractColimit) = apex(colim)
cocone(colim::AbstractColimit) = colim.cocone
apex(colim::AbstractColimit) = apex(cocone(colim))
legs(colim::AbstractColimit) = legs(cocone(colim))

Base.iterate(colim::AbstractColimit, args...) = iterate(cocone(colim), args...)
Base.eltype(colim::AbstractColimit) = eltype(cocone(colim))
Base.length(colim::AbstractColimit) = length(cocone(colim))

""" Colimit in a category.
"""
@auto_hash_equals struct Colimit{Ob,Diagram,Cocone<:Multicospan{Ob}} <:
    AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
end

const Initial{Ob} = AbstractColimit{Ob,<:EmptyDiagram}
const BinaryCoproduct{Ob} = AbstractColimit{Ob,<:ObjectPair}
const Coproduct{Ob} = AbstractColimit{Ob,<:DiscreteDiagram}
const BinaryPushout{Ob} = AbstractColimit{Ob,<:Span}
const Pushout{Ob} = AbstractColimit{Ob,<:Multispan}
const BinaryCoequalizer{Ob} = AbstractColimit{Ob,<:ParallelPair}
const Coequalizer{Ob} = AbstractColimit{Ob,<:ParallelMorphisms}

coproj1(colim::Union{BinaryCoproduct,BinaryPushout}) = first(legs(colim))
coproj2(colim::Union{BinaryCoproduct,BinaryPushout}) = last(legs(colim))
proj(coeq::Coequalizer) = only(legs(coeq))

""" Algorithm for computing colimits.
"""
abstract type ColimitAlgorithm end

# Generic (co)limits
####################

""" Limit of a diagram.

To define limits in a category with objects `Ob`, override the method
`limit(::FreeDiagram{Ob})` for general limits or `limit(::D)` with suitable type
`D <: FixedShapeFreeDiagram{Ob}` for limits of specific shape, such as products
or equalizers.

See also: [`colimit`](@ref)
"""
limit(diagram; kw...) = limit(diagram_type(diagram), diagram; kw...)
limit(diagram, ::Nothing; kw...) = limit(diagram; kw...) # alg == nothing

""" Colimit of a diagram.

To define colimits in a category with objects `Ob`, override the method
`colimit(::FreeDiagram{Ob})` for general colimits or `colimit(::D)` with
suitable type `D <: FixedShapeFreeDiagram{Ob}` for colimits of specific shape,
such as coproducts or coequalizers.

See also: [`limit`](@ref)
"""
colimit(diagram; kw...) = colimit(diagram_type(diagram), diagram; kw...)
colimit(diagram, ::Nothing; kw...) = colimit(diagram; kw...) # alg == nothing

""" Universal property of (co)limits.

Compute the morphism whose existence and uniqueness is guaranteed by the
universal property of (co)limits.

See also: [`limit`](@ref), [`colimit`](@ref).
"""
function universal end

# Specific (co)limits
#####################

""" Terminal object.

To implement for a type `T`, define the method `limit(::EmptyDiagram{T})`.
"""
terminal(T::Type; kw...) = limit(EmptyDiagram{T}(); kw...)

""" Initial object.

To implement for a type `T`, define the method `colimit(::EmptyDiagram{T})`.
"""
initial(T::Type; kw...) = colimit(EmptyDiagram{T}(); kw...)

""" Unique morphism into a terminal object.

To implement for a type `T`, define the method
`universal(::Terminal{T}, ::SMultispan{0,T})`.
"""
delete(A::T) where T = delete(terminal(T), A)
delete(lim::Terminal, A) = universal(lim, SMultispan{0}(A))

""" Unique morphism out of an initial object.

To implement for a type `T`, define the method
`universal(::Initial{T}, ::SMulticospan{0,T})`.
"""
create(A::T) where T = create(initial(T), A)
create(colim::Initial, A) = universal(colim, SMulticospan{0}(A))

""" Product of objects.

To implement for a type `T`, define the method `limit(::ObjectPair{T})` and/or
`limit(::DiscreteDiagram{T})`.
"""
product(A, B; kw...) = limit(ObjectPair(A, B); kw...)
product(As::AbstractVector; kw...) = limit(DiscreteDiagram(As); kw...)

""" Coproduct of objects.

To implement for a type `T`, define the method `colimit(::ObjectPair{T})` and/or
`colimit(::DiscreteDiagram{T})`.
"""
coproduct(A, B; kw...) = colimit(ObjectPair(A, B); kw...)
coproduct(As::AbstractVector; kw...) = colimit(DiscreteDiagram(As); kw...)

""" Equalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `limit(::ParallelPair{T})` and/or
`limit(::ParallelMorphisms{T})`.
"""
equalizer(f, g; kw...) = limit(ParallelPair(f, g); kw...)
equalizer(fs::AbstractVector; kw...) = limit(ParallelMorphisms(fs); kw...)

""" Coequalizer of morphisms with common domain and codomain.

To implement for a type `T`, define the method `colimit(::ParallelPair{T})` or
`colimit(::ParallelMorphisms{T})`.
"""
coequalizer(f, g; kw...) = colimit(ParallelPair(f, g); kw...)
coequalizer(fs::AbstractVector; kw...) = colimit(ParallelMorphisms(fs); kw...)

""" Pullback of a pair of morphisms with common codomain.

To implement for a type `T`, define the method `limit(::Cospan{T})` and/or
`limit(::Multicospan{T})` or, if you have already implemented products and
equalizers, rely on the default implementation.
"""
pullback(f, g; kw...) = limit(Cospan(f, g); kw...)
pullback(fs::AbstractVector; kw...) = limit(Multicospan(fs); kw...)

""" Pushout of a pair of morphisms with common domain.

To implement for a type `T`, define the method `colimit(::Span{T})` and/or
`colimit(::Multispan{T})` or, if you have already implemented coproducts and
coequalizers, rely on the default implementation.
"""
pushout(f, g; kw...) = colimit(Span(f, g); kw...)
pushout(fs::AbstractVector; kw...) = colimit(Multispan(fs); kw...)

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(f, g) = pair(product(codom(f), codom(g)), f, g)
pair(fs::AbstractVector) = pair(product(map(codom, fs)), fs)
pair(lim::Union{BinaryProduct,BinaryPullback}, f, g) =
  universal(lim, Span(f, g))
pair(lim::Union{Product,Pullback}, fs::AbstractVector) =
  universal(lim, Multispan(fs))

""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(f, g) = copair(coproduct(dom(f), dom(g)), f, g)
copair(fs::AbstractVector) = copair(coproduct(map(dom, fs)), fs)
copair(colim::Union{BinaryCoproduct,BinaryPushout}, f, g) =
  universal(colim, Cospan(f, g))
copair(colim::Union{Coproduct,Pushout}, fs::AbstractVector) =
  universal(colim, Multicospan(fs))

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
factorize(lim::Equalizer, h) = universal(lim, SMultispan{1}(h))
factorize(colim::Coequalizer, h) = universal(colim, SMulticospan{1}(h))

""" Pushout complement: extend composable pair to a pushout square.

[Pushout complements](https://ncatlab.org/nlab/show/pushout+complement) are the
essential ingredient for double pushout (DPO) rewriting.
"""
pushout_complement(f, g) = pushout_complement(ComposablePair(f, g))

""" Can a pushout complement be constructed for a composable pair?

Even in nice categories, this is not generally possible.
"""
can_pushout_complement(f, g) = can_pushout_complement(ComposablePair(f, g))

# (Co)cartesian monoidal categories
###################################

""" Define cartesian monoidal structure using limits.

Implements an instance of [`CartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
macro cartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: CartesianCategory, otimes, ⊗, munit, braid, σ,
      mcopy, delete, pair, proj1, proj2, Δ, ◊

    @instance CartesianCategory{$Ob, $Hom} begin
      @import dom, codom, compose, ⋅, id, munit, delete, pair

      otimes(A::$Ob, B::$Ob) = ob(product(A, B))

      function otimes(f::$Hom, g::$Hom)
        π1, π2 = product(dom(f), dom(g))
        pair(product(codom(f), codom(g)), π1⋅f, π2⋅g)
      end

      function braid(A::$Ob, B::$Ob)
        AB, BA = product(A, B), product(B, A)
        pair(BA, proj2(AB), proj1(AB))
      end

      mcopy(A::$Ob) = pair(id(A),id(A))
      proj1(A::$Ob, B::$Ob) = proj1(product(A, B))
      proj2(A::$Ob, B::$Ob) = proj2(product(A, B))
    end

    otimes(As::AbstractVector{<:$Ob}) = ob(product(As))

    function otimes(fs::AbstractVector{<:$Hom})
      Π, Π′ = product(map(dom, fs)), product(map(codom, fs))
      pair(Π′, map(compose, legs(Π), fs))
    end

    munit(::Type{T}) where T <: $Ob = ob(terminal(T))
  end)
end

""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`CocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface.
"""
macro cocartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: CocartesianCategory, oplus, ⊕, mzero, swap,
      plus, zero, copair, coproj1, coproj2

    @instance CocartesianCategory{$Ob, $Hom} begin
      @import dom, codom, compose, ⋅, id, mzero, copair

      oplus(A::$Ob, B::$Ob) = ob(coproduct(A, B))

      function oplus(f::$Hom, g::$Hom)
        ι1, ι2 = coproduct(codom(f), codom(g))
        copair(coproduct(dom(f), dom(g)), f⋅ι1, g⋅ι2)
      end

      function swap(A::$Ob, B::$Ob)
        AB, BA = coproduct(A, B), coproduct(B, A)
        copair(AB, coproj2(BA), coproj1(BA))
      end

      plus(A::$Ob) = copair(id(A),id(A))
      zero(A::$Ob) = create(A)
      coproj1(A::$Ob, B::$Ob) = coproj1(coproduct(A, B))
      coproj2(A::$Ob, B::$Ob) = coproj2(coproduct(A, B))
    end

    oplus(As::AbstractVector{<:$Ob}) = ob(coproduct(As))

    function oplus(fs::AbstractVector{<:$Hom})
      ⊔, ⊔′ = coproduct(map(dom, fs)), coproduct(map(codom, fs))
      copair(⊔, map(compose, fs, legs(⊔′)))
    end

    mzero(::Type{T}) where T <: $Ob = ob(initial(T))
  end)
end

# (Co)limit algorithms
######################

# Specialize (co)limits
#----------------------

""" Meta-algorithm attempting to reduce general limits to common special cases.

Specifically, reduce limits of free diagrams that happen to be discrete to
products. TODO: Handle pullbacks similarly.
"""
@Base.kwdef struct SpecializeLimit <: LimitAlgorithm
  fallback::Union{LimitAlgorithm,Nothing} = nothing
end

limit(diagram, alg::SpecializeLimit) = limit(diagram, alg.fallback)

function limit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
               alg::SpecializeLimit) where {Ob,Hom}
  if is_discrete(dom(F))
    return limit(DiscreteDiagram(collect_ob(F), Hom), alg)
  end
  limit(F, alg.fallback)
end
limit(diagram::FreeDiagram, alg::SpecializeLimit) =
  limit(FinDomFunctor(diagram), alg)

function limit(Xs::DiscreteDiagram{Ob,Hom,Obs},
               alg::SpecializeLimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    return limit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), alg)
  end
  limit(Xs, alg.fallback)
end

""" Meta-algorithm attempting to reduce general colimits to common special cases.

Dual to [`SpecializeLimit`](@ref).
"""
@Base.kwdef struct SpecializeColimit <: ColimitAlgorithm
  fallback::Union{ColimitAlgorithm,Nothing} = nothing
end

colimit(diagram, alg::SpecializeColimit) = colimit(diagram, alg.fallback)

function colimit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
                 alg::SpecializeColimit) where {Ob,Hom}
  if is_discrete(dom(F))
    return colimit(DiscreteDiagram(collect_ob(F), Hom), alg)
  end
  colimit(F, alg.fallback)
end
colimit(diagram::FreeDiagram, alg::SpecializeColimit) =
  colimit(FinDomFunctor(diagram), alg)

function colimit(Xs::DiscreteDiagram{Ob,Hom,Obs},
                 alg::SpecializeColimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    return colimit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), alg)
  end
  colimit(Xs, alg.fallback)
end

""" Limit of a singleton diagram.
"""
struct SingletonLimit{Ob,Diagram<:SingletonDiagram{Ob}} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
end

cone(lim::SingletonLimit) = let x = only(lim.diagram)
  SMultispan{1}(x, id(x))
end
universal(::SingletonLimit, cone::Multispan) = only(cone)

limit(diagram::SingletonDiagram, ::SpecializeLimit) = SingletonLimit(diagram)

""" Colimit of a singleton diagram.
"""
struct SingletonColimit{Ob,Diagram<:SingletonDiagram{Ob}} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
end

cocone(colim::SingletonColimit) = let x = only(colim.diagram)
  SMulticospan{1}(x, id(x))
end
universal(::SingletonColimit, cocone::Multicospan) = only(cocone)

colimit(diagram::SingletonDiagram, ::SpecializeColimit) =
  SingletonColimit(diagram)

# Composite (co)limits
#---------------------

""" Compute pullback by composing a product with an equalizer.

See also: [`ComposeCoproductCoequalizer`](@ref).
"""
struct ComposeProductEqualizer <: LimitAlgorithm end

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pushout, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback{Ob, Diagram<:Multicospan, Cone<:Multispan{Ob},
    Prod<:Product, Eq<:Equalizer} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  prod::Prod
  eq::Eq
end

function limit(cospan::Multicospan, ::ComposeProductEqualizer)
  prod = product(feet(cospan))
  (ι,) = eq = equalizer(map(compose, legs(prod), legs(cospan)))
  cone = Multispan(map(π -> ι⋅π, legs(prod)))
  CompositePullback(cospan, cone, prod, eq)
end

function universal(lim::CompositePullback, cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

""" Compute pushout by composing a coproduct with a coequalizer.

See also: [`ComposeProductEqualizer`](@ref).
"""
struct ComposeCoproductCoequalizer <: ColimitAlgorithm end

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Ob, Diagram<:Multispan, Cocone<:Multicospan{Ob},
    Coprod<:Coproduct, Coeq<:Coequalizer} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  coprod::Coprod
  coeq::Coeq
end

function colimit(span::Multispan, ::ComposeCoproductCoequalizer)
  coprod = coproduct(feet(span))
  (π,) = coeq = coequalizer(map(compose, legs(span), legs(coprod)))
  cocone = Multicospan(map(ι -> ι⋅π, legs(coprod)))
  CompositePushout(span, cocone, coprod, coeq)
end

function universal(lim::CompositePushout, cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end

# Bipartite (co)limits
#---------------------

""" Compute a limit by reducing the diagram to a free bipartite diagram.
"""
struct ToBipartiteLimit <: LimitAlgorithm end

""" Limit computed by reduction to the limit of a free bipartite diagram.
"""
struct BipartiteLimit{Ob, Diagram, Cone<:Multispan{Ob},
                      Lim<:AbstractLimit} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limit::Lim
end

function limit(F::Union{Functor,FreeDiagram}, ::ToBipartiteLimit)
  d = BipartiteFreeDiagram(F)
  lim = limit(d)
  cone = Multispan(apex(lim), map(incident(d, :, :orig_vert₁),
                                  incident(d, :, :orig_vert₂)) do v₁, v₂
    if v₁ == 0
      e = first(incident(d, v₂, :tgt))
      compose(legs(lim)[src(d, e)], hom(d, e))
    else
      legs(lim)[v₁]
    end
  end)
  BipartiteLimit(F, cone, lim)
end

function universal(lim::BipartiteLimit, cone::Multispan)
  lim = lim.limit
  cone = Multispan(apex(cone), legs(cone)[lim.diagram[:orig_vert₁]])
  universal(lim, cone)
end

""" Compute a colimit by reducing the diagram to a free bipartite diagram.
"""
struct ToBipartiteColimit <: ColimitAlgorithm end

""" Limit computed by reduction to the limit of a free bipartite diagram.
"""
struct BipartiteColimit{Ob, Diagram, Cocone<:Multicospan{Ob},
                        Colim<:AbstractColimit} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimit::Colim
end

function colimit(F::Union{Functor,FreeDiagram}, ::ToBipartiteColimit)
  d = BipartiteFreeDiagram(F, colimit=true)
  colim = colimit(d)
  cocone = Multicospan(apex(colim), map(incident(d, :, :orig_vert₁),
                                        incident(d, :, :orig_vert₂)) do v₁, v₂
    if v₂ == 0
      e = first(incident(d, v₁, :src))
      compose(hom(d, e), legs(colim)[tgt(d, e)])
    else
      legs(colim)[v₂]
    end
  end)
  BipartiteColimit(F, cocone, colim)
end

function universal(colim::BipartiteColimit, cocone::Multicospan)
  colim = colim.colimit
  cocone = Multicospan(apex(cocone), legs(cocone)[colim.diagram[:orig_vert₂]])
  universal(colim, cocone)
end

# Limits in category of diagrams
#-------------------------------
"""
Decompose a product morphism into a composition of canonical generators, i.e.
morphisms that have exactly one non-ID component

Assumes we have a dictionary that takes us, e.g., from a tuple (f: A->B, idₓ) to
the product morphism (f,idₓ): A×X⟶B×X
"""
function product_decompose(f::Vector, hdict::Dict)
  curr = id.(dom.(f))
  res, n = [], length(f)
  for (i,m) in enumerate(f)
    if (m isa HomExpr{:compose}) margs = m.args
    elseif (m isa HomExpr{:generator}) margs = [m]
    else margs = []
    end
    for marg in margs
      args = tuple([j == i ? marg : curr[j] for j in 1:n]...)
      push!(res, hdict[args])
    end
    curr[i] = id(codom(m))
  end
  return compose(res)
end

"""
Product of finitely-presented categories has the cartesian product of ob
generators as its objects. Its morphisms are generated by, for each morphism in
the underlying categories, taking the product of that morphism with the
identity morphism of all objects of all other categories. For example:

 h                  f   g
X->Y multiplied by A->B<-C is:

                 (f,idY) (g, idY)
                 YA -> YB  <-  YC
         (h,idA) |     |(h,idB) | (h,idC)
                 XA -> XB  <-  XC
                 (f,idX) (g, idX)


For any pair (e.g. f:A->B,h:X->Y), we get a naturality square
                (f,idX)
          A x X  ---->  B x X
            |             |
  (id(A),h) |             | (id(B),h)
          A x Y  --->  B x Y
              (f,id(Y))

For any triple, we get a naturality cube (six naturality squares), and so on.
TODO: figure out whether or not we also require 8 path equations to go from one
corner of the cube to the other, or if that is derivable from the equalities on
the faces of the cube. My intuition is: yes we need these additional equations.
Currently we have no tests that fail due to this.
"""
function product(Xs::AbstractVector{<: FinCatPresentation}; kw...)
  # Get cartesian product of obs and hosm
  obs = collect(Iterators.product([ob_generators(x)  for x in Xs]...))[:]

  homs = vcat(map(enumerate(Xs)) do (i,X)
    vcat(map(hom_generators(X)) do h
      p = Iterators.product([id.(ob_generators(Y)) for (j,Y) in enumerate(Xs) if j!=i]...)
      map(collect.(collect(p)[:])) do hgens
        tuple(insert!(Vector{Any}(hgens), i, h)...)
      end
    end...)
  end...)

  obdict = Dict([v=>k for (k,v) in enumerate(obs)])

  # Create new presentation with tuple-looking names
  p = Presentation(FreeSchema)

  ogens = [Ob(FreeSchema, Symbol(o)) for o in obs]
  map(ogens) do g add_generator!(p, g) end
  hgens = Dict{Any,Any}(map(homs) do hs
    src, tgt = map([dom, codom]) do get
      ogens[obdict[tuple([get(X, h) for (h, X) in zip(hs,Xs)]...)]]
    end
    hs => add_generator!(p, Hom(Symbol(hs), src, tgt))
  end)
  for (k,v) in zip(obs, ogens)
    hgens[tuple(id.(k)...)] = id(v)
  end

  # Add naturality squares
  for i in 1:(length(Xs)-1)
    hgi = hom_generators(Xs[i])
    for j in i+1:length(Xs)
      hgj = hom_generators(Xs[j])
      fun(iarg, jarg, args) = map(1:length(Xs)) do k
        if k==i iarg elseif k==j jarg else args[k] end end
      for hij in Iterators.product(hgi, hgj)
        hi, hj = hij
        args = fun([nothing], [nothing], [id.(ob_generators(x))  for x in Xs])
        for hs in Iterators.product(args...)
          (di, cdi), (dj, cdj) = [id.([dom(x), codom(x)]) for x in hij]
          xs = [hi=>dj, cdi=>hj, di=>hj, hi=>cdj] # naturality square
          a1,a2,b1,b2 = [product_decompose(fun(x1,x2,hs), hgens) for (x1,x2) in xs]
          add_equation!(p, compose(a1,a2), compose(b1,b2))
        end
      end
    end
  end

  # Add equations from base categories
  for (i, X) in enumerate(Xs)
    for lr in equations(X)
      is = [j == i ? [nothing] : id.(ob_generators(x))
            for (j, x) in enumerate(Xs)]
      for bkgrnd in Iterators.product(is...)
        l_, r_ = map(lr) do t
          comps = (t isa HomExpr{:id} || t isa HomExpr{:generator}) ? [t] : t.args
          comps_ = map(comps) do comp
            hgens[tuple([k==i ? comp : c for (k,c) in enumerate(bkgrnd)]...)]
          end
          compose(comps_)
        end
        add_equation!(p, l_, r_)
      end
    end
  end

  # Create projection maps
  apx = FinCat(p)
  ls = map(enumerate(Xs)) do (i, x)
    os, hs = map([obs, homs]) do oldgens
      Dict([Symbol(o) => o[i] for o in oldgens])
    end
    FinDomFunctor(os, hs, apx, x)
  end
  Limit(DiscreteDiagram(Xs), Multispan(ls))
end

"""
TODO: handle equations by filtering those including symbols not in osyms ∪ hsyms
"""
function equalizer(fs::AbstractVector{<:FinDomFunctor{<:FinCatPresentation}})
  # Check fs are parallel finfunctors
  I, _ = only.(Set.([dom.(fs), codom.(fs)]))

  # identify things that maps make equal
  Eo, Eh = map(zip([ob_generators, hom_generators], [ob_map, hom_map])) do (g, m)
     [x for x in g(I) if length(Set([m(f, x) for f in fs])) == 1]
  end
  osyms, hsyms = Set.([Symbol.(Eo), Symbol.(Eh)])

  # Create new sub-presentation of the domain
  p = Presentation(FreeSchema)
  for g in vcat(Eo,Eh) add_generator!(p, g) end

  # Create inclusion morphism
  obs, homs = map([osyms,hsyms]) do syms
    Dict{Symbol,Symbol}(s=>s for s in syms)
  end
  l1 = FinDomFunctor(obs, homs, FinCat(p), I)
  Limit(ParallelMorphisms(fs), Multispan([l1]))
end

"""
Preserves the original name of the inputs if it is unambiguous, otherwise
disambiguates with index in original input. E.g. (A,B)⊔(B,C) → (A,B#1,B#2,C)
"""
function coproduct(Xs::AbstractVector{<: FinCatPresentation}; kw...)
  # Collect all generators and identify conflicting names
  all_ob = vcat(ob_generators.(Xs)...)
  all_hom = vcat(hom_generators.(Xs)...)
  conflict_obs = Set([i for i in all_ob if count(==(i), all_ob) > 1])
  conflict_homs = Set([i for i in all_hom if count(==(i), all_hom) > 1])

  # Create new disjoint union presentation
  p = Presentation(FreeSchema)
  ogens = Dict(vcat(map(enumerate(Xs)) do (i, X)
    map(ob_generators(X)) do o
      (i,o) => Ob(FreeSchema, Symbol("$o" * (o ∈ conflict_obs ? "#$i" : "")))
    end
  end...))
  map(values(ogens)) do g add_generator!(p, g) end

  hgens = Dict(vcat(map(enumerate(Xs)) do (i, X)
    map(hom_generators(X)) do h
      n = Symbol("$h" * (h ∈ conflict_homs ? "#$i" : ""))
      s, t = ogens[(i, dom(X,h))], ogens[(i, codom(X,h))]
      (i,h) => add_generator!(p, Hom(n, s, t))
    end
  end...))

  # Create legs into equationless target to help us project the equations
  for  (i,x) in enumerate(Xs)
    os, hs = map(zip([ob_generators,hom_generators], [ogens,hgens])) do (get, g)
      Dict([Symbol(o) => Symbol(g[(i,o)]) for o in get(x)])
    end
    l = FinDomFunctor(os, hs, x, FinCat(p))
    for (e1,e2) in equations(x)
      add_equation!(p, hom_map(l, e1), hom_map(l, e2))
    end
  end

  # Create legs into equationful target
  ls = map(enumerate(Xs)) do (i,x)
    os, hs = map(zip([ob_generators,hom_generators], [ogens,hgens])) do (get, g)
      Dict([Symbol(o) => Symbol(g[(i,o)]) for o in get(x)])
    end
    FinDomFunctor(os, hs, x, FinCat(p))
  end

  Colimit(DiscreteDiagram(Xs), Multicospan(ls))
end

"""
TODO: handle equations
"""
function coequalizer(fs::AbstractVector{<:FinDomFunctor{<:FinCatPresentation}})
  # Check inputs are parallel finfunctors
  I, J = only.(Set.([dom.(fs), codom.(fs)]))

  # Generate equivalence class reps for the generators of codomain
  f1 = first(fs)
  og, hg = ob_generators, hom_generators
  odict, hdict = map(zip([og, hg], [ob_map, hom_map])) do (gen, map_)
    class = IntDisjointSets(length(gen(J)))
    inds = Dict(v=>k for (k,v) in enumerate(gen(J)))
    map(gen(I)) do o
      map(fs) do f
        union!(class, inds[map_(f1, o)], inds[map_(f, o)])
      end
    end
    Dict(o => gen(J)[find_root!(class, i)] for (i, o) in enumerate(gen(J)))
  end

  # Create presentation from equivalence classes
  p = Presentation(FreeSchema)
  obs, homs = [Dict() for _ in 1:2]
  for i in sort(collect(Set(values(odict))), by=string)
    os = sort([string(k) for (k, v) in collect(odict) if v==i])
    g = add_generator!(p, Ob(FreeSchema, Symbol("[$(join(os,","))]")))
    for o in os
      obs[Symbol(o)] = g
    end
  end
  for i in sort(collect(Set(values(hdict))), by=string)
    hs = sort([k for (k, v) in collect(hdict) if v==i], by=string)
    s, t = map([dom, codom]) do get
      obs[Symbol(get(J, first(hs)))]
    end
    g = add_generator!(p, Hom(Symbol("[$(join(string.(hs),","))]"), s, t))
    for h in hs
      homs[Symbol(h)] = Symbol(g)
    end
  end
  l1 = FinDomFunctor(obs, homs, J, FinCat(p))
  Colimit(ParallelMorphisms(fs), Multicospan([l1]))
end


"""
A generator a that is mapped to generators X,Y,... in the span is matched to the
ob generator (X, Y, ...) in the product.

An edge f:a->b that is mapped to morphisms α,β,γ in the span is matched to a
composite of hom generators that yields the morphism (α,β,γ) in the product.
This composition sequence starts with (α, id(src(β)), id(src(γ))) and ends with
(id(tgt(α)), id(tgt(β)), γ)
"""
function universal(p::Product{<:FinCat}, sp::Multispan)
  a_p, a_sp = apex.([p, sp])
  obs = Dict(map(ob_generators(a_sp)) do o
    p_tgts = [ob_map(l, o) for l in legs(sp)]
    for po in ob_generators(a_p)
      if p_tgts == [ob_map(l, po) for l in legs(p)]
        return o => po
      end
    end
    error("o $o (w/ tgts $p_tgts) not found")
  end)
  homs = Dict(map(hom_generators(a_sp)) do h
    doms, codoms = map([dom, codom]) do get
      id.([get(codom(l), hom_map(l, h)) for l in legs(sp)])
    end
    # Find the morphism generators we want to map to
    h_comps = map(enumerate(legs(sp))) do (i, l)
      # Identify morphism by what the product maps it to
      h_tgt = map(1:length(legs(sp))) do j
        if j < i      codoms[j]
        elseif j == i hom_map(l, h)
        else          doms[j]
        end
      end
      """
      WARNING: if the hom map component is composite, it won't be found below.
      Need to break up compose into components with `product_decompose`
      """
      # Locate this morphism based on what it maps to
      for ph in vcat(hom_generators(a_p), id.(ob_generators(a_p)))
        if h_tgt == [hom_map(l, ph) for l in legs(p)]
          return ph
        end
      end
      error("h $h -> htgt $h_tgt not found")
    end
    h => compose(h_comps)
  end)
  FinFunctor(obs, homs, a_sp, a_p)
end


function universal(cp::Coproduct{<:FinCat}, csp::Multicospan)
  a_cp, a_csp = apex.([cp, csp])
  obs, homs = Dict(), Dict()
  for (cpl, cspl) in zip(legs(cp),legs(csp))
    for o in ob_generators(dom(cpl))
      obs[ob_map(cpl, o)] = ob_map(cspl, o)
    end
    for h in hom_generators(dom(cpl))
      homs[hom_map(cpl, h)] = hom_map(cspl, h)
    end
  end
  FinFunctor(obs, homs, a_cp, a_csp)
end

function universal(eq::Equalizer{<:FinCat}, f::FinDomFunctor)
  FinFunctor(ob_map(f), hom_map(f), dom(f), apex(eq))
end

function universal(ceq::Coequalizer{<:FinCat}, f::FinDomFunctor)
  obs = Dict([ob_map(proj(ceq), k) => v for (k,v) in ob_map(f)])
  homs = Dict([hom_map(proj(ceq), k) => v for (k,v) in hom_map(f)])
  FinFunctor(obs, homs, apex(ceq), codom(f))
end

end
