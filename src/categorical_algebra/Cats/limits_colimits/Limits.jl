module Limits

export Limit, LimitImpl, cone, limit, pullback, LimitCone, CompositeLimit, 
       terminal, product,  delete, incl, proj1, proj2, pair, equalizer, 
       NestedLoopJoin, SortMergeJoin, HashJoin, SmartJoin,
       ComposeProductEqualizer, CartesianMonoidal

using StructEquality
using ACSets: incident

using GATlab
using GATlab.Syntax.TheoryInterface: WithModel
import GATlab: getvalue

using .....Theories: dom, codom, id, compose, ThCartesianCategory
import .....Theories: incl, terminal, product, delete, proj1, proj2, 
                      factorize, pair, equalizer, universal, otimes, munit, ⊗

using .....Graphs: nv₁

using ...Categories: Category, TypeCat, obtype, homtype
using ...FreeDiagrams
using ...FreeDiagrams: DiagramImpl, objects, getcategory
import ...FreeDiagrams: ob, apex, legs
using ...FinFunctors: FinDomFunctor

using ..LimitsColimits: LimColim, LimitAlgorithm, DefaultAlg
import ..LimitsColimits: _universal, cone_cocone

import .ThCartesianCategory: otimes, munit

# Generic implementation type 
#############################

abstract type LimitImpl end

ob(lim::LimitImpl) = apex(cone(lim))

apex(lim::LimitImpl) = ob(lim)

cone(lim::LimitImpl) = lim.cone # by default, assume LimitImpl has `cone` field

"""
A `Limit` stores a diagram as well as the result of taking its limit
"""
@struct_hash_equal struct Limit <: LimColim
  diag::Diagram
  impl::LimitImpl
end 

cone_cocone(l::Limit) = cone(l) # `cocone` not defined on Limits

cone(lim::Limit) = cone(getvalue(lim))

# Algorithms
############



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


# Limit Implementations 
#######################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct LimitCone <: LimitImpl
  cone::Multispan
end

""" Default limit for a multispan """
Limit(dia::Diagram, c::Multispan) = Limit(dia, LimitCone(c))

Limit(dia::Diagram, c::Span) = Limit(dia, Multispan(c))

# Composite Limit
#---------------

""" Limit of general diagram computed by product-then-filter. """
@struct_hash_equal struct CompositeLimit{Hom} <: LimitImpl
  cone::Multispan
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
struct CompositePullback <: LimitImpl
  cone::Multispan
  prod::Limit
  eq::Limit
end


"""
`CompositePullback` is constructed via applying the `ComposeProductEqualizer` 
algorithm to a cospan.
"""
function limit(cospan::Multicospan, m::Category, ::ComposeProductEqualizer)
  prod = product(feet(cospan), m)
  (ι,) = eq = equalizer(map(compose[getvalue(m)], legs(prod), legs(cospan)), m)
  cone = Multispan(map(π -> compose[getvalue(m)](ι,π), legs(prod)))
  Limit(Diagram(cospan, m), CompositePullback(cone, prod, eq))
end

function _universal(::Multicospan, ::Category, lim::CompositePullback, 
                    cone::Multispan)
  factorize(lim.eq, universal(lim.prod, cone))
end

# Singleton
#----------

""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonLimit{Ob,Hom} <: LimitImpl
  ob::Ob
  i::Hom
  function SingletonLimit(d::SingletonDiagram, m::Category)
    o = only(objects(d))
    i = id(m,o)
    new{typeof(o),typeof(i)}(o, i)
  end
end

ob(s::SingletonLimit) = s.ob

legs(s::SingletonLimit) = [s.i]

cone(s::SingletonLimit) = Multispan(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
function limit(d::SingletonDiagram, m::Category, ::DefaultAlg)
  SingletonLimit(d, m)
  Limit(Diagram(d, m), SingletonLimit(d, m))
end

 _universal(::Multicospan, ::Category, lim::SingletonLimit, cone::Multispan) = 
  only(cone)


# Generic limits
####################
limit(d::Diagram; alg=DefaultAlg()) = limit(getvalue(d), getvalue(getcategory(d)), alg)

""" Limit of TypeCat determined by dispatching on its implementation """
limit(d, c::TypeCat, alg) = limit(d, getvalue(c), alg)


limit(d::FreeDiagram{Ob,Hom}, m::Category; alg=DefaultAlg()) where {Ob,Hom} = 
  limit(BipartiteFreeDiagram{Ob,Hom}(d; colimit=false), m, alg)

limit(d::FinDomFunctor; alg=DefaultAlg(), kw...) = 
  limit(FreeDiagram(d), codom(d); alg, kw...)

proj1(lim::Limit) = let (l,_) = legs(lim); l end

proj2(lim::Limit) = let (_,l) = legs(lim); l end

incl(eq::Limit) = only(legs(eq))

# Named limits
##################

terminal(m::Category; alg=DefaultAlg()) = limit(Diagram(m); alg)

product(xs::AbstractVector, model::Category; alg=DefaultAlg()) = 
  limit(DiscreteDiagram(xs), model, alg)

equalizer(f, g, model::Category; alg=DefaultAlg()) = equalizer([f,g], model; alg)

equalizer(xs::AbstractVector, model::Category; alg=DefaultAlg()) = 
  limit(ParallelMorphisms(xs), model, alg)

pullback(fs::AbstractVector, model::Category; alg=DefaultAlg()) = 
limit(Multicospan(fs), model, alg)

pullback(f, g, model::Category; alg=DefaultAlg()) = 
limit(Multicospan([f,g]), model, alg)

# Dispatch on Categories
########################

""" Universal dispatches on the implementation of a Category """
_universal(d::DiagramImpl, c::Category, ci::LimitImpl, csp::Multispan) = 
  _universal(d, getvalue(c), ci, csp)

  """ Universal dispatches on the implementation of a TypeCat """
_universal(d::DiagramImpl, c::TypeCat, ci::LimitImpl, csp::Multispan) = 
  _universal(d, getvalue(c), ci, csp)

limit(d::DiagramImpl, c::Category, alg; kw...) = limit(d, getvalue(c), alg; kw...)

limit(d::DiagramImpl, c::TypeCat, alg; kw...) = limit(d, getvalue(c), alg; kw...)


# Universal interface
#####################

"""
Apply the universal property of a limit to a multispan

Optionally validate the span 
"""
function universal(c::Limit, x::Multispan; check=false) 
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

universal(c::Limit, x::Span; check=false) = universal(c, Multispan(x); check)

# Named universal maps 
######################

function delete(l::Limit, x)
  getvalue(l.diag) isa EmptyDiagram || error(
    "Can only call `delete` on EmptyDiagram limits")
  universal(l, Multispan(x, homtype(l)[]))
end

delete(x, mod::Category) = delete(terminal(mod), x)

""" Factor morphism through (co)equalizer, via the universal property.

To implement for equalizers of type `T`, define the method
`universal(::Equalizer{T}, ::SMultispan{1,T})`. For coequalizers of type `T`,
define the method `universal(::Coequalizer{T}, ::SMulticospan{1,T})`.
"""
function factorize(lim::Limit, h)
  getvalue(lim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(lim, Multispan(dom(h), [h]))
end

""" Pairing of morphisms: universal property of products/pullbacks.

To implement for products of type `T`, define the method
`universal(::BinaryProduct{T}, ::Span{T})` and/or
`universal(::Product{T}, ::Multispan{T})` and similarly for pullbacks.
"""
pair(f, g, m::Category) = pair([f,g], m)

pair(fs::AbstractVector,m::Category) = pair(product(codom.(fs), m), fs)

pair(lim::Limit, fs::AbstractVector) = universal(lim, Multispan(fs))

pair(lim::Limit, f1::T, f2::T) where {T} = pair(lim, [f1, f2])

# Monoidal
##########


""" Define cartesian monoidal structure using limits.

Implements an instance of [`ThCartesianCategory`](@ref) assuming that finite
products have been implemented following the limits interface.
"""
struct CartesianMonoidal{Ob,Hom} <: Model{Tuple{Ob,Hom}} 
  cat::Category
  CartesianMonoidal(c::Category) = new{obtype(c), homtype(c)}(c)
end

getvalue(c::CartesianMonoidal) = c.cat

@instance ThCartesianCategory{Ob, Hom} [model::CartesianMonoidal{Ob,Hom}
                                       ] where {Ob,Hom} begin
  @import Ob, Hom, dom, codom, compose, ⋅, →, id, munit, pair, delete

  otimes(A::Ob, B::Ob) = ob(product([A, B], getvalue(model)))

  function otimes(f::Hom, g::Hom)
    M = getvalue(model)
    π1, π2 = product([dom(f), dom(g)], M)
    pair(product([codom(f), codom(g)], M), compose(M, π1,f), compose(M, π2, g))
  end

  function braid(A::Ob, B::Ob)
    AB, BA = product([A, B], getvalue(model)), product([B, A], getvalue(model))
    pair(BA, proj2(AB), proj1(AB))
  end

  mcopy(A::Ob) = pair(id(A),id(A), model)
  proj1(A::Ob, B::Ob) = proj1(product([A, B], getvalue(model)))
  proj2(A::Ob, B::Ob) = proj2(product([A, B], getvalue(model)))
end

otimes(m::WithModel{CartesianMonoidal{Ob,Hom}}, As::AbstractVector{<:Ob}
      ) where {Ob,Hom} = ob(product(As, getvalue(getvalue(m))))

function otimes(m::WithModel{CartesianMonoidal{Ob,Hom}}, fs::AbstractVector{<:Hom}) where {Ob,Hom}
  C = getvalue(getvalue(m))
  Π, Π′ = product(map(dom, fs), C), product(map(codom, fs), C)
  pair(Π′, map((x,y)->compose(C,x,y), legs(Π), fs))
end

munit(m::WithModel{CartesianMonoidal{Ob,Hom}}) where {Ob,Hom} = 
  ob(terminal(getvalue(getvalue(m))))

end # module
