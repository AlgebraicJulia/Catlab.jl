""" Limits and colimits in a category.
"""
module Limits
export AbstractLimit, AbstractColimit, Limit, Colimit,
  LimitAlgorithm, ColimitAlgorithm,
  ob, cone, cocone, apex, legs, limit, colimit, universal,
  Terminal, Initial, terminal, initial, delete, create, factorize, image, coimage, epi_mono,
  BinaryProduct, Product, product, proj1, proj2, pair,
  BinaryPullback, Pullback, pullback,
  BinaryEqualizer, Equalizer, equalizer, incl,
  BinaryCoproduct, Coproduct, coproduct, coproj1, coproj2, copair,
  BinaryPushout, Pushout, pushout,
  BinaryCoequalizer, Coequalizer, coequalizer, proj,
  @cartesian_monoidal_instance, @cocartesian_monoidal_instance,
  ComposeProductEqualizer, ComposeCoproductCoequalizer,
  SpecializeLimit, SpecializeColimit, ToBipartiteLimit, ToBipartiteColimit,
  product_fincat

using StructEquality
using StaticArrays: StaticVector, SVector

using ACSets
using GATlab
using ...Theories
import ...Theories: dom, codom, ob, hom,
  terminal, product, proj1, proj2, equalizer, incl,
  initial, coproduct, coproj1, coproj2, coequalizer, proj,
  delete, create, pair, copair, factorize, universal
using ..FinCats, ..FreeDiagrams
using ..FinCats: FinCatPresentation
import ..FreeDiagrams: apex, legs

# Data types for limits
#######################

""" Abstract type for limit in a category.

The standard concrete subtype is [`Limit`](@ref), although for computational
reasons certain categories may use different subtypes to include extra data.
"""
abstract type AbstractLimit{Ob,Diagram} end

ob(lim::AbstractLimit) = apex(lim)
cone(lim::AbstractLimit) = lim.cone
"""Synonymous with `ob` in the case of `Limit`s, but 
present here to allow a `Limit` to be implicitly 
treated like a `Multispan`."""
apex(lim::AbstractLimit) = apex(cone(lim)) 
legs(lim::AbstractLimit) = legs(cone(lim))

Base.iterate(lim::AbstractLimit, args...) = iterate(cone(lim), args...)
Base.eltype(lim::AbstractLimit) = eltype(cone(lim))
Base.length(lim::AbstractLimit) = length(cone(lim))

""" Limit in a category.
"""
@struct_hash_equal struct Limit{Ob,Diagram,Cone<:Multispan{Ob}} <:
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
@struct_hash_equal struct Colimit{Ob,Diagram,Cocone<:Multicospan{Ob}} <:
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

""" 
    universal(lim,cone)

Universal property of (co)limits.

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

"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f) = equalizer(legs(pushout(f,f))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f) = coequalizer(legs(pullback(f,f))...)

"""
The image and coimage are isomorphic. We get this isomorphism using univeral
properties.

      CoIm′ ╌╌> I ↠ CoIm
        ┆ ⌟     |
        v       v
        I   ⟶  R ↩ Im
        |       ┆
        v    ⌜  v
        R ╌╌> Im′
"""
function epi_mono(f)
  Im, CoIm = image(f), coimage(f)
  iso = factorize(Im, factorize(CoIm, f))
  return ComposablePair(proj(CoIm) ⋅ iso, incl(Im))
end

# (Co)cartesian monoidal categories
###################################

""" Define cartesian monoidal structure using limits.

Implements an instance of [`ThCartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
macro cartesian_monoidal_instance(Ob, Hom)
  thcc = ThCartesianCategory.Meta.theory
  instance_body = quote
    @import Ob, Hom, →, dom, codom, compose, ⋅, id, munit, delete, pair

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

  instance_code = ModelInterface.generate_instance(
    ThCartesianCategory.Meta.theory,
    ThCartesianCategory,
    Dict(zip(sorts(thcc), [Ob, Hom])),
    nothing,
    [],
    instance_body;
    escape=false
  )

  esc(quote
    import Catlab.Theories: ThCartesianCategory, otimes, ⊗, munit, braid, σ,
      mcopy, delete, pair, proj1, proj2, Δ, ◊

    $instance_code

    otimes(As::AbstractVector{<:$Ob}) = ob(product(As))

    function otimes(fs::AbstractVector{<:$Hom})
      Π, Π′ = product(map(dom, fs)), product(map(codom, fs))
      pair(Π′, map(compose, legs(Π), fs))
    end

    munit(::Type{T}) where T <: $Ob = ob(terminal(T))
  end)
end

""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`ThCocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface.
"""
macro cocartesian_monoidal_instance(Ob, Hom)
  esc(quote
    import Catlab.Theories: ThCocartesianCategory, oplus, ⊕, mzero, swap,
      plus, zero, copair, coproj1, coproj2

    @instance ThCocartesianCategory{$Ob, $Hom} begin
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

""" Meta-algorithm that reduces general limits to common special cases.

Reduces limits of free diagrams that happen to be discrete to products. If this
fails, fall back to the given algorithm (if any).

TODO: Reduce free diagrams that are (multi)cospans to (wide) pullbacks.
"""
@Base.kwdef struct SpecializeLimit <: LimitAlgorithm
  fallback::Union{LimitAlgorithm,Nothing} = nothing
end

limit(diagram, alg::SpecializeLimit) = limit(diagram, alg.fallback)

function limit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
               alg::SpecializeLimit) where {Ob,Hom}
  if is_discrete(dom(F))
    limit(DiscreteDiagram(collect_ob(F), Hom), SpecializeLimit())
  else
    limit(F, alg.fallback)
  end
end
limit(diagram::FreeDiagram, alg::SpecializeLimit) =
  limit(FinDomFunctor(diagram), alg)

function limit(Xs::DiscreteDiagram{Ob,Hom,Obs},
               alg::SpecializeLimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    limit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), SpecializeLimit())
  else
    limit(Xs, alg.fallback)
  end
end

""" Meta-algorithm that reduces general colimits to common special cases.

Dual to [`SpecializeLimit`](@ref).
"""
@Base.kwdef struct SpecializeColimit <: ColimitAlgorithm
  fallback::Union{ColimitAlgorithm,Nothing} = nothing
end

colimit(diagram, alg::SpecializeColimit) = colimit(diagram, alg.fallback)

function colimit(F::FinDomFunctor{<:FinCat{Int},<:TypeCat{Ob,Hom}},
                 alg::SpecializeColimit) where {Ob,Hom}
  if is_discrete(dom(F))
    colimit(DiscreteDiagram(collect_ob(F), Hom), SpecializeColimit())
  else
    colimit(F, alg.fallback)
  end
end
colimit(diagram::FreeDiagram, alg::SpecializeColimit) =
  colimit(FinDomFunctor(diagram), alg)

function colimit(Xs::DiscreteDiagram{Ob,Hom,Obs},
                 alg::SpecializeColimit) where {Ob,Hom,Obs}
  if !(Obs <: StaticVector) && length(Xs) <= 3
    colimit(DiscreteDiagram(SVector{length(Xs)}(ob(Xs)), Hom), SpecializeColimit())
  else
    colimit(Xs, alg.fallback)
  end
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
violates the abstraction. Everything that you can do with a pullback, including
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


# FIXME: make this similar to how colimits are treated
function limit(F::Union{Functor,FreeDiagram,FixedShapeFreeDiagram}, ::ToBipartiteLimit)
  d = BipartiteFreeDiagram(F)
  lim = limit(d)
  cone = Multispan(apex(lim), map(incident(d, :, :orig_vert₁),
                                  incident(d, :, :orig_vert₂)) do v₁, v₂
    if isempty(v₁)
      e = first(incident(d, only(v₂), :tgt))
      compose(legs(lim)[src(d, e)], hom(d, e))
    else
      legs(lim)[only(v₁)]
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

function colimit(F::FixedShapeFreeDiagram, ::ToBipartiteColimit)
  kwarg = F isa DiscreteDiagram ? Dict(:colimit=>true) : Dict()
  d = BipartiteFreeDiagram(F; kwarg...)
  colim = colimit(d)
  return BipartiteColimit(F, cocone(colim), colim)
end 

function colimit(F::Union{T,FreeDiagram}, ::ToBipartiteColimit) where {T<:Functor}
  d = BipartiteFreeDiagram(F, colimit=true)
  colim = colimit(d)
  cocone = Multicospan(apex(colim), map(incident(d, :, :orig_vert₁),
                                        incident(d, :, :orig_vert₂)) do v₁, v₂
    if isempty(v₂)
      e = first(incident(d, only(v₁), :src))
      compose(hom(d, e), legs(colim)[tgt(d, e)])
    else
      legs(colim)[only(v₂)]
    end
  end)
  BipartiteColimit(F, cocone, colim)
end

function universal(colim::BipartiteColimit, cocone::Multicospan)
  colim = colim.colimit
  cocone = Multicospan(apex(cocone), legs(cocone)[cocone_indices(colim.diagram)])
  universal(colim, cocone)
end

# Product of FinCats
####################

"""
Product of finitely-presented categories has the cartesian product of ob
generators as its objects. Its morphisms are generated by, for each morphism in
the underlying categories, taking the product of that morphism with the
identity morphism of all objects of all other categories. For example:

 h                  f   g
X->Y multiplied by A->B<-C is:

                  (f,idY)  (g, idY)
                 YA  ->  YB   <-  YC
         (h,idA) ↑       ↑(h,idB)  ↑(h,idC)
                 XA  ->  XB   <-  XC
                  (f,idX)  (g, idX)

For any pair (e.g. f:A->B, h:X->Y), we get a naturality square

                (f,idX)
          A × X  ---->  B × X
            |             |
  (id(A),h) |             | (id(B),h)
          A × Y  --->   B × Y
              (f,id(Y))

For any triple, we get a naturality cube (six naturality squares), and so on.
"""
function product(Xs::AbstractVector{<:FinCatPresentation}; kw...)
  # Get cartesian product of obs and homs
  #--------------------------------------
  # obs as component tuples
  obs = collect(Iterators.product([ob_generators(x)  for x in Xs]...))[:]
  obdict = Dict([v => k for (k, v) in enumerate(obs)]) # get index from Ob-tuple

  # component tuples for the generating morphisms 
  homs = vcat(map(enumerate(Xs)) do (i, X)
    vcat(map(hom_generators(X)) do h
      p = [id.(ob_generators(Y)) for (j,Y) in enumerate(Xs) if j != i]
      map(collect.(collect(Iterators.product(p...))[:])) do hgens
        tuple(insert!(Vector{Any}(hgens), i, h)...)
      end
    end...)
  end...)

  # Create new presentation with tuple-looking names
  #-------------------------------------------------
  p = Presentation(FreeSchema)
  ogens = Ob.(Ref(FreeSchema), Symbol.(obs))
  add_generator!.(Ref(p), ogens)
  
  # Lookup mapping from tuples of morphisms to generating morphisms in product
  # Note the only morphisms here are ones with exactly one non-id component
  hgens = Dict{Tuple,FreeSchema.Hom}(map(homs) do hs
    hs => add_generator!(p, Hom(Symbol(hs), map([dom, codom]) do dom_codom
      ogens[obdict[tuple([dom_codom(X, h) for (h, X) in zip(hs, Xs)]...)]]
    end...))
  end)

  # Also add to hom-dictionary the morphisms which have only id components.
  for (k,v) in zip(obs, ogens)
    hgens[tuple(id.(k)...)] = id(v)
  end

  # Add multiple naturality squares for each unordered pair of FinCats
  #-------------------------------------------------------------------
  for i in 1:(length(Xs) - 1), j in (i+1):length(Xs)
    # Construct a composite morphism with id for all non-i non-j components.
    fun(iarg, jarg, args) = tuple(map(1:length(Xs)) do k
      if k==i iarg elseif k==j jarg else args[k] end 
    end...)
    # Commutative squares for each morphism in Xᵢ and morphism in Xⱼ
    for (hᵢ, hⱼ) in Iterators.product(hom_generators.(getindex.(Ref(Xs), [i, j]))...)
      (dᵢ, cdᵢ), (dⱼ, cdⱼ) = [id.([dom(x), codom(x)]) for x in [hᵢ, hⱼ]]
      # A square for each combination of objects in the non-i, non-j FinCats
      args = [id.(ob_generators(x)) for (k, x) in enumerate(Xs) if k ∉ (i,j)]
      for hs in Vector{Any}.(collect.(Iterators.product(args...)))
        a₁,a₂,b₁,b₂ = map([[hᵢ, dⱼ], [cdᵢ, hⱼ], [dᵢ, hⱼ], [hᵢ, cdⱼ]]) do x₁x₂
          hs′ = deepcopy(hs)
          insert!.(Ref(hs′), [i, j], x₁x₂) # insert i,j components in right spot
          hgens[tuple(hs′...)]             # morphism for a side of nat. square
        end
        add_equation!(p, a₁⋅a₂, b₁⋅b₂)
      end
    end
  end

  # Add equations from base categories
  #-----------------------------------
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
  #-----------------------
  ls = map(enumerate(Xs)) do (i, Xᵢ)
    os, hs = map([obs, homs]) do generator_tuples
      Dict([Symbol(o) => o[i] for o in generator_tuples])
    end
    FinDomFunctor(os, hs, FinCat(p), Xᵢ)
  end
  Limit(DiscreteDiagram(Xs), Multispan(ls))
end


end
