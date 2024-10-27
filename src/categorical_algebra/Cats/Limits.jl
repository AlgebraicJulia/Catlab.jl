module Limits 

export Limit, Colimit, cone, cocone, limit, colimit, pullback, pushout, 
       LimitCone, ColimitCocone, CompositeLimit,CompositeColimit, 
       image, coimage,epi_mono, bundle_legs,
       initial, terminal, product, coproduct, create, delete, objects,
       proj, incl, proj1, proj2, coproj1, coproj2, ob, factorize,
       pair, copair, universal, equalizer, coequalizer,
       @cartesian_monoidal_instance, @cocartesian_monoidal_instance,
       NestedLoopJoin, SortMergeJoin, HashJoin, ComposeProductEqualizer,
       DefaultAlg, ComposeCoproductCoequalizer, SmartJoin, CompositePushout

using StructEquality
using StaticArrays: SVector
using GATlab
import GATlab: getvalue
using ACSets: incident

using ..FreeDiagrams
import ..FreeDiagrams: apex, legs
using ..FreeDiagrams: cone_objects, cocone_objects, objects, getcategory
using ....Graphs: nv₁, nv₂
using ....Theories: dom, codom
import ....Theories: initial, terminal, product, coproduct, create, delete, 
                    proj, incl, proj1, proj2, coproj1, coproj2, ob, factorize,
                    pair, copair, universal, equalizer, coequalizer

using .ThCategory 
const C{Ob,Hom} = Model{Tuple{Ob,Hom}}

# Data structures for (co)limits
################################

# Abstract types
#---------------

abstract type LimColim end # for shared code between limits and colimits

getvalue(l::LimColim) = l.impl

diagram(l::LimColim) = l.diagram

ob(colim::LimColim) = apex(colim)

apex(lim::LimColim) = apex(cone_cocone(lim)) 

legs(lim::LimColim) = legs(cone_cocone(lim))

Base.iterate(lim::LimColim, x...) = iterate(cone_cocone(lim), x...)

Base.length(lim::LimColim) = length(cone_cocone(lim))


abstract type LimitImpl{Ob, Hom} end

ob(lim::LimitImpl) = apex(cone(lim))

apex(lim::LimitImpl) = ob(lim)

cone(lim::LimitImpl) = lim.cone # by default, assume LimitImpl has `cone` field


abstract type ColimitImpl{Ob, Hom} end

ob(lim::ColimitImpl) = apex(cocone(lim))

apex(lim::ColimitImpl) = ob(lim)

cocone(lim::ColimitImpl) = lim.cocone # by default, assume CoimitImpl has `cocone` field

# Limits 
#-------

@struct_hash_equal struct Limit{Ob, Hom} <: LimColim
  diag::Diagram{Ob,Hom}
  impl::LimitImpl{<:Ob,<:Hom}
end 

cone_cocone(l::Limit) = cone(l) # `cocone` not defined on Limits

cone(lim::Limit) = cone(getvalue(lim))

# Colimits 
#---------

@struct_hash_equal struct Colimit{Ob, Hom} <: LimColim
  diag::Diagram{Ob, Hom}
  impl::ColimitImpl{<:Ob, <:Hom}
end 

cone_cocone(l::Colimit) = cocone(l) # `cone` not defined on Colimits

cocone(colim::Colimit) = cocone(getvalue(colim))

# (Co)Limit algorithms
######################

abstract type LimitAlgorithm end

@struct_hash_equal struct DefaultAlg <: LimitAlgorithm end 

""" Algorithm for limit of cospan or multicospan with feet being finite sets.

In the context of relational databases, such limits are called *joins*. The
trivial join algorithm is [`NestedLoopJoin`](@ref), which is algorithmically
equivalent to the generic algorithm `ComposeProductEqualizer`. The algorithms
[`HashJoin`](@ref) and [`SortMergeJoin`](@ref) are usually much faster. If you
are unsure what algorithm to pick, use [`SmartJoin`](@ref).
"""
abstract type JoinAlgorithm <: LimitAlgorithm end

""" This is the naive algorithm for computing joins. """
@struct_hash_equal struct NestedLoopJoin <: JoinAlgorithm end 

""" [Sort-merge join](https://en.wikipedia.org/wiki/Sort-merge_join) algorithm.
"""
@struct_hash_equal struct SortMergeJoin <: JoinAlgorithm end 

""" [Hash join](https://en.wikipedia.org/wiki/Hash_join) algorithm.
"""
@struct_hash_equal struct HashJoin <: JoinAlgorithm end

""" Meta-algorithm for joins that attempts to pick an appropriate algorithm. """
@struct_hash_equal struct SmartJoin <: JoinAlgorithm end

""" Compute pullback by composing a product with an equalizer.

See also: [`ComposeCoproductCoequalizer`](@ref).
"""
@struct_hash_equal struct ComposeProductEqualizer <: LimitAlgorithm end 

@struct_hash_equal struct ComposeCoproductCoequalizer <: LimitAlgorithm end 

""" Compute colimit of finite sets whose elements are meaningfully named.

This situation seems to be mathematically uninteresting but is practically
important. The colimit is computed by reduction to the skeleton of **FinSet**
(`FinSet{Int}`) and the names are assigned afterwards, following some reasonable
conventions and add tags where necessary to avoid name clashes.
"""
@struct_hash_equal struct NamedColimit <: LimitAlgorithm end 

# Limit Implementations 
#######################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct LimitCone{Ob,Hom} <: LimitImpl{Ob,Hom}
  cone::Multispan{Ob, Hom}
end

""" Default limit for a multispan """
Limit(dia::Diagram, c::Multispan) = Limit(dia, LimitCone(c))

Limit(dia::Diagram, c::Span) = Limit(dia, Multispan(c))

# Composite Limit
#---------------

""" Limit of general diagram computed by product-then-filter. """
@struct_hash_equal struct CompositeLimit{Ob,Hom} <: LimitImpl{Ob,Hom}
  cone::Multispan{Ob, Hom}
  prod::Limit
  incl::Hom # Inclusion for the "multi-equalizer" in general formula.
end


# Composite pullback
#-------------------

""" Pullback formed as composite of product and equalizer.

The fields of this struct are an implementation detail; accessing them directly
violates the abstraction. Everything that you can do with a pullback, including
invoking its universal property, should be done through the generic interface
for limits.

See also: [`CompositePushout`](@ref).
"""
struct CompositePullback{Ob, Hom} <: LimitImpl{Ob,Hom}
  cone::Multispan{Ob, Hom}
  prod::Limit
  eq::Limit
end


"""
`CompositePullback` is constructed via applying the `ComposeProductEqualizer` 
algorithm to a cospan.
"""
function limit(cospan::Multicospan{<:Ob,<:Hom}, m::C{Ob,Hom}, 
               ::ComposeProductEqualizer) where {Ob, Hom}
  prod = product(feet(cospan), m)
  (ι,) = eq = equalizer(map(compose[m], legs(prod), legs(cospan)), m)
  cone = Multispan{Ob,Hom}(map(π -> compose[m](ι,π), legs(prod)))
  Limit(Diagram(cospan, m), CompositePullback(cone, prod, eq))
end

function _universal(::Multicospan, ::C{Ob,Hom}, lim::CompositePullback, 
                    cone::Multispan{<:Ob,<:Hom}) where {Ob,Hom}
  factorize(lim.eq, universal(lim.prod, cone))
end

# Singleton
#----------

""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonLimit{Ob,Hom} <: LimitImpl{Ob,Hom}
  ob::Ob
  i::Hom
  function SingletonLimit(d::D, m::C{Ob,Hom}) where {Ob,Hom,D<:SingletonDiagram}
    o = only(objects(d))
    new{Ob,Hom}(o, id[m](o))
  end
end

ob(s::SingletonLimit) = s.ob

legs(s::SingletonLimit) = [s.i]

cone(s::SingletonLimit{Ob,Hom}) where {Ob,Hom} = 
  Multispan{Ob,Hom}(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
function limit(d::SingletonDiagram{<:Ob,<:Hom}, m::C{Ob,Hom}, ::DefaultAlg
              ) where {Ob, Hom}
  SingletonLimit(d, m)
  Limit(Diagram(d, m), SingletonLimit(d, m))
end

 _universal(::Multicospan, ::C{Ob,Hom}, lim::SingletonLimit, 
       cone::Multispan{<:Ob,<:Hom}) where {Ob,Hom} = only(cone)


# Colimit Implementations 
#########################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct ColimitCocone{Ob,Hom} <: ColimitImpl{Ob,Hom}
  cocone::Multicospan{Ob, Hom}
end

""" Default colimit for a multicospan """
Colimit(dia::Diagram, c::Multicospan) = Colimit(dia, ColimitCocone(c))

Colimit(dia::Diagram, c::Cospan) = Colimit(dia, Multicospan(c))

# Composite colimit
#------------------

""" Colimit of general diagram computed by coproduct and projection """
@struct_hash_equal struct CompositeColimit{Ob,Hom} <: ColimitImpl{Ob,Hom}
  cocone::Multicospan{Ob, Hom}
  coprod::Colimit
  proj::Hom 
end


# Composite pushout 
#------------------

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout{Ob,Hom} <: ColimitImpl{Ob,Hom}
  cocone::Multicospan{Ob,Hom}
  coprod::Colimit
  coeq::Colimit
end

function colimit(span::Multispan{<:Ob,<:Hom}, m::C{Ob,Hom}, 
                ::ComposeCoproductCoequalizer) where {Ob, Hom}
  coprod = coproduct(feet(span), m)
  (π,) = coeq = coequalizer(map(compose[m], legs(span), legs(coprod)), m)
  cocone = Multicospan{Ob,Hom}(map(ι -> compose[m](ι,π), legs(coprod)))
  Colimit(Diagram(span, m), CompositePushout(cocone, coprod, coeq))
end

function _universal(::Multispan, ::C{Ob,Hom}, lim::CompositePushout, 
                  cone::Multicospan{<:Ob,<:Hom}) where {Ob,Hom}
  factorize(lim.coeq, universal(lim.coprod, cone))
end


# Singleton
#----------

""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonColimit{Ob,Hom} <: ColimitImpl{Ob,Hom}
  ob::Ob
  i::Hom
  function SingletonColimit(d::D, m::C{Ob,Hom}) where {Ob,Hom,D<:SingletonDiagram}
    o = only(objects(d))
    new{Ob,Hom}(o, id[m](o))
  end
end

ob(s::SingletonColimit) = s.ob

legs(s::SingletonColimit) = [s.i]

cocone(s::SingletonColimit{Ob,Hom}) where {Ob,Hom} = 
  Multicospan{Ob,Hom}(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
function colimit(d::SingletonDiagram{<:Ob,<:Hom}, m::C{Ob,Hom}, ::DefaultAlg
              ) where {Ob, Hom}
  SingletonColimit(d, m)
  Colimit(Diagram(d, m), SingletonColimit(d, m))
end

 _universal(::Multispan, ::C{Ob,Hom}, lim::SingletonColimit, 
            cocone::Multicospan{<:Ob,<:Hom}) where {Ob,Hom} = only(cocone)


# Generic (co)limits
####################

limit(d::Diagram; alg=DefaultAlg()) = limit(getvalue(d), getcategory(d), alg)

limit(d::FreeDiagram{Ob,Hom}, m::C{Ob,Hom}; alg=DefaultAlg()) where {Ob,Hom} = 
  limit(BipartiteFreeDiagram{Ob,Hom}(d; colimit=false), m, alg)

colimit(d::Diagram; alg=DefaultAlg()) = colimit(getvalue(d), getcategory(d), alg)

colimit(d::FreeDiagram{Ob,Hom}, m::C{Ob,Hom}; alg=DefaultAlg()) where {Ob,Hom} = 
  colimit(BipartiteFreeDiagram(d; colimit=true), m, alg)

proj(coeq::Colimit) = only(legs(coeq))

proj1(lim::Limit) = let (l,_) = legs(lim); l end

proj2(lim::Limit) = let (_,l) = legs(lim); l end

incl(eq::Limit) = only(legs(eq))

coproj1(colim::Colimit) = let (l,_) = legs(colim); l end

coproj2(colim::Colimit) = let (_,l) = legs(colim); l end

# Named (co)limits
##################

terminal(m::Model; alg=DefaultAlg()) = limit(Diagram(m); alg)

initial(m::Model; alg=DefaultAlg()) = colimit(Diagram(m); alg)

product(xs::AbstractVector, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom} = 
  limit(DiscreteDiagram(xs, Hom), model, alg)

coproduct(xs::AbstractVector, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom} = 
  colimit(DiscreteDiagram(xs, Hom), model, alg)

equalizer(f::H, g::H, model::C{Ob,Hom}; alg=DefaultAlg()
         ) where {Ob, Hom, H<:Hom} = equalizer([f,g], model; alg)

equalizer(xs::AbstractVector, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom} = 
  limit(ParallelMorphisms(xs), model, alg)

coequalizer(f::H, g::H, model::C{Ob,Hom}; alg=DefaultAlg()
           ) where {Ob, Hom, H<:Hom} = coequalizer([f,g], model; alg)

coequalizer(xs::AbstractVector, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom} = 
  colimit(ParallelMorphisms(xs), model, alg)

pullback(fs::AbstractVector{H}, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom, H<:Hom} = limit(Multicospan{Ob,Hom}(fs), model, alg)

pullback(f::H,g::H, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom, H<:Hom} = 
  limit(Multicospan{Ob,Hom}([f,g]), model, alg)

pushout(fs::AbstractVector{H}, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom, H<:Hom} = limit(Multispan{Ob,Hom}(fs), model, alg)

pushout(f::H,g::H, model::C{Ob,Hom}; alg=DefaultAlg()) where {Ob, Hom, H<:Hom} = 
  colimit(Multispan{Ob,Hom}([f,g]), model, alg)

"""https://en.wikipedia.org/wiki/Image_(category_theory)#Second_definition"""
image(f::H, m::C{Ob,Hom}) where {Ob, Hom, H<:Hom} = 
  equalizer(legs(pushout(f,f, m))...)

"""https://en.wikipedia.org/wiki/Coimage"""
coimage(f::H, m::C{Ob,Hom}) where {Ob, Hom, H<:Hom} = 
  coequalizer(legs(pullback(f, f, m))...)


# Universal interface
#####################

"""
Apply the universal property of a limit to a multispan

Optionally validate the span 
"""
function universal(c::Limit{Ob,Hom}, x::Multispan{<:Ob,<:Hom}; check=false
                  )::Hom where {Ob,Hom}
  if check
    co = cone_objects(c.diag)
    feet(x) == co || error("Span $(feet(x)) doesn't match cone_objects $co")
    bp = BipartiteFreeDiagram(getvalue(c.diag); colimit=false)

    for i in 1:nv₁(bp)
      allequal(map(incident(bp, i, :src)) do j 
        x[bp[j, :tgt]] ⋅ bp[j, :hom]
      end) || error("Non-commuting cone for ob₁ $i")
    end
  end
  _universal(getvalue(c.diag), getcategory(c.diag), getvalue(c), x)
end

function universal(c::Limit{Ob,Hom}, x::Span{<:Ob,<:Hom}; check=false
                  )::Hom where {Ob,Hom} 
  universal(c, Multispan(x); check)
end

"""
Apply the universal property of a colimit to a multicospan

Optionally validate the cospan.
"""
function universal(c::Colimit{Ob,Hom}, x::Multicospan{<:Ob,<:Hom}; check=false
                  )::Hom where {Ob,Hom} 
  if check
    co = cocone_objects(c.diag)
    feet(x) == co || error("Cospan $(feet(x)) doesn't match cocone_objects $co")
    bp = BipartiteFreeDiagram(getvalue(c.diag); colimit=true)

    for i in 1:nv₂(bp)
      allequal(map(incident(bp, i, :tgt)) do j 
        bp[j, :hom]  ⋅ x[bp[j, :tgt]] 
      end) || error("Non-commuting cocone for ob₂ $i")
    end
  end
  _universal(getvalue(c.diag), getcategory(c.diag), getvalue(c), x)
end

function universal(c::Colimit{Ob,Hom}, x::Cospan{<:Ob,<:Hom}; check=false
                  )::Hom where {Ob,Hom}  
  universal(c, Multicospan(x); check)
end


"""
Implement this for each diagram impl + category combination.

`_universal` expects the following arguments: 
- the diagram impl 
- the category the diagram is in 
- the (co)cone result of the (co)Limit
- the multi(co)span to which we are applying the universal property
"""
function _universal end 

# Named universal maps 
######################

function create(l::Colimit{Ob,Hom}, x::O) where {Ob,Hom,O<:Ob} 
  getvalue(l.diag) isa EmptyDiagram || error(
    "Can only call `create` on EmptyDiagram colimits")
  universal(l, Multicospan{Ob,Hom}(x))
end

function delete(l::Limit{Ob,Hom}, x::O) where {Ob,Hom,O<:Ob} 
  getvalue(l.diag) isa EmptyDiagram || error(
    "Can only call `delete` on EmptyDiagram limits")
  universal(l, Multispan{Ob,Hom}(x))
end

create(x::Ob, mod::C{Ob,Hom}) where {Ob,Hom} = create(initial(mod), x)

delete(x::Ob, mod::C{Ob,Hom}) where {Ob,Hom} = delete(terminal(mod), x)

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
function factorize(lim::Limit{Ob,Hom}, h::H) where {Ob,Hom, H<:Hom} 
  getvalue(lim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(lim, Multispan(dom(h), [h]))
end

function factorize(colim::Colimit{Ob,Hom}, h::Hom) where {Ob,Hom} 
  getvalue(colim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(colim, Multicospan{Ob,Hom}([h]))
end

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(f, g, m::C{Ob,Hom}) where {Ob,Hom} = pair([f,g], m)

pair(fs::AbstractVector{<:Hom},m::C{Ob,Hom}) where {Ob,Hom} = 
  pair(product(codom.(fs), m), fs)

pair(lim::Limit{Ob,Hom}, fs::AbstractVector{<:Hom}) where {Ob,Hom} =
  universal(lim, Multispan{Ob,Hom}(fs))

pair(lim::Limit{Ob,Hom}, f1::T, f2::T) where {Ob,Hom,T<:Hom} = 
  pair(lim, [f1, f2])

""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(f, g, m::C{Ob,Hom}) where {Ob,Hom} = copair([f,g], m)

copair(fs::AbstractVector{<:Hom},m::C{Ob,Hom}) where {Ob,Hom} = 
  copair(coproduct(codom.(fs), m), fs)

copair(colim::Colimit{Ob,Hom}, fs::AbstractVector{<:Hom}) where {Ob,Hom} =
  universal(colim, Multicospan{Ob,Hom}(fs))

copair(lim::Colimit{Ob,Hom}, f1::T,f2::T) where {Ob,Hom,T<:Hom} = 
  copair(lim, [f1, f2])

# Other (co)limit constructions
###############################

""" Bundle together legs of a multi(co)span.

For example, calling `bundle_legs(span, SVector((1,2),(3,4)))` on a multispan
with four legs gives a span whose left leg bundles legs 1 and 2 and whose right
leg bundles legs 3 and 4. Note that in addition to bundling, this function can
also permute legs and discard them.

The bundling is performed using the universal property of (co)products, which
assumes that these (co)limits exist.
"""
bundle_legs(span::Multispan{Ob,Hom}, indices, m::C{Ob,Hom}) where {Ob,Hom} =
  Multispan{Ob,Hom}(apex(span), map(i -> bundle_leg(span, i, m), indices))
  
bundle_legs(cospan::Multicospan{Ob,Hom}, indices, m::C{Ob,Hom}) where {Ob,Hom} =
  Multicospan{Ob,Hom}(apex(cospan), map(i -> bundle_leg(cospan, i, m), indices))

bundle_leg(x::Union{Multispan,Multicospan}, i::Int, m::C{Ob,Hom}
          ) where {Ob,Hom} = legs(x)[i]
bundle_leg(x::Union{Multispan,Multicospan}, i::Tuple, m::C{Ob,Hom}
           ) where {Ob,Hom} = bundle_leg(x, SVector(i), m)
bundle_leg(span::Multispan, i::AbstractVector{Int}, m::C{Ob,Hom}
          ) where {Ob,Hom} = pair(legs(span)[i], m)
bundle_leg(cospan::Multicospan, i::AbstractVector{Int}, m::C{Ob,Hom}  
          ) where {Ob,Hom}  = copair(legs(cospan)[i], m)


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
function epi_mono(f::H, m::C{Ob,Hom}) where {Ob, Hom, H<:Hom}
  Im, CoIm = image(f, m), coimage(f, m)
  iso = factorize(Im, factorize(CoIm, f))
  ComposablePair{Ob,Hom}(proj(CoIm) ⋅ iso, incl(Im))
end

# Macros 
########

""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`ThCocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface. Assumes that 
the model takes no parameters nor type parameters.
"""
macro cocartesian_monoidal_instance(Ob, Hom, M)
  esc(quote
    using GATlab.Syntax.TheoryInterface: WithModel

    import Catlab.Theories: ThCocartesianCategory, oplus, ⊕, mzero, swap,
      plus, zero, copair, coproj1, coproj2

    @instance ThCocartesianCategory{$Ob, $Hom} [model::$M] begin
      @import dom, codom, compose, ⋅, id, mzero, copair

      oplus(A::$Ob, B::$Ob) = ob(coproduct([A, B], $M()))

      function oplus(f::$Hom, g::$Hom)
        ι1, ι2 = coproduct([codom(f), codom(g)], $M())
        copair(coproduct([dom(f), dom(g)], $M()), compose[$M()](f,ι1), compose[$M()](g,ι2))
      end

      function swap(A::$Ob, B::$Ob)
        AB, BA = coproduct([A, B], $M()), coproduct([B, A], $M())
        copair(AB, coproj2(BA), coproj1(BA))
      end

      plus(A::$Ob) = copair(id(A),id(A), $M())
      zero(A::$Ob) = create(A, $M())
      coproj1(A::$Ob, B::$Ob) = coproj1(coproduct([A, B], $M()))
      coproj2(A::$Ob, B::$Ob) = coproj2(coproduct([A, B], $M()))
    end

    oplus(::WithModel{$M}, As::AbstractVector{<:$Ob}; context=(;)) = ob(coproduct(As, $M()))

    function oplus(::WithModel{$M}, fs::AbstractVector{<:$Hom}; context=(;))
      ⊔, ⊔′ = coproduct(map(dom, fs)), coproduct(map(codom, fs))
      copair(⊔, map(compose, fs, legs(⊔′)))
    end

    mzero(::WithModel{$M}; context=(;)) = ob(initial($M()))
  end)
end

""" Define cartesian monoidal structure using limits.

Implements an instance of [`ThCartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface. Assumes that the 
model takes no parameters nor type parameters.
"""
macro cartesian_monoidal_instance(Ob, Hom, M)
  esc(quote
    using GATlab.Syntax.TheoryInterface: WithModel

    import Catlab.Theories: ThCartesianCategory, otimes, munit, braid, 
      mcopy, pair, proj1, proj2

    @instance ThCartesianCategory{$Ob, $Hom} [model::$M] begin
      @import Ob, Hom, dom, codom, compose, ⋅, →, id, munit, pair, delete

      otimes(A::$Ob, B::$Ob) = ob(product([A, B], $M()))

      function otimes(f::$Hom, g::$Hom)
        π1, π2 = product([dom(f), dom(g)], $M())
        pair(product([codom(f), codom(g)], $M()), 
             compose[$M()](π1,f), compose[$M()](π2, g))
      end

      function braid(A::$Ob, B::$Ob)
        AB, BA = product([A, B], $M()), product([B, A], $M())
        pair(BA, proj2(AB), proj1(AB))
      end

      mcopy(A::$Ob) = pair(id(A),id(A), $M())
      proj1(A::$Ob, B::$Ob) = proj1(product([A, B], $M()))
      proj2(A::$Ob, B::$Ob) = proj2(product([A, B], $M()))
    end

    otimes(::WithModel{$M}, As::AbstractVector{<:$Ob}; context=(;)) = ob(product(As, $M()))

    function otimes(::WithModel{$M}, fs::AbstractVector{<:$Hom}; context=(;))
      Π, Π′ = product(map(dom, fs)), product(map(codom, fs))
      pair(Π′, map(compose, legs(Π), fs))
    end

    munit(::WithModel{$M}; context=(;)) = ob(terminal($M()))
  end)
end

end # module 
