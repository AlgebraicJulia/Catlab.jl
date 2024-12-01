module Colimits 
export Colimit, ColimitImpl, initial, cocone, colimit, pushout,ColimitCocone, 
       CompositeColimit, coproduct, create,copair, proj, coproj1, coproj2, 
       coequalizer, ComposeCoproductCoequalizer,  CompositePushout, 
       CocartesianMonoidal, NamedColimit

using StructEquality
using ACSets: incident
using GATlab
using GATlab.Syntax.TheoryInterface: WithModel
import GATlab: getvalue

using .....Graphs: nv₂
using .....Theories: dom, codom, id, compose, ThCocartesianCategory
import .....Theories: proj, initial, coproduct, create, coproj1, coproj2, 
                      factorize, copair, coequalizer, universal, ⊕, oplus

using ...Categories: Category, TypeCat, obtype, homtype
using ...FreeDiagrams
using ...FreeDiagrams: DiagramImpl, objects, getcategory
import ...FreeDiagrams: ob, apex, legs
using ...FinFunctors: FinDomFunctor

using ..LimitsColimits: LimColim, LimitAlgorithm, DefaultAlg
import ..LimitsColimits: _universal, cone_cocone

import .ThCocartesianCategory: oplus, mzero

# Generic implementation type 
#############################

abstract type ColimitImpl end

ob(lim::ColimitImpl) = apex(cocone(lim))

apex(lim::ColimitImpl) = ob(lim)

cocone(lim::ColimitImpl) = lim.cocone # by default, assume ColimitImpl has `cocone` field

"""
A `Colimit` stores a diagram as well as the result of taking its colimit
"""
@struct_hash_equal struct Colimit <: LimColim
  diag::Diagram
  impl::ColimitImpl
end 

cone_cocone(l::Colimit) = cocone(l) # `cone` not defined on Colimits

cocone(colim::Colimit) = cocone(getvalue(colim))


# Colimit algorithms
######################

@struct_hash_equal struct ComposeCoproductCoequalizer <: LimitAlgorithm end 

""" Compute colimit of finite sets whose elements are meaningfully named.

This situation seems to be mathematically uninteresting but is practically
important. The colimit is computed by reduction to the skeleton of **FinSet**
(`FinSet{Int}`) and the names are assigned afterwards, following some reasonable
conventions and add tags where necessary to avoid name clashes.
"""
@struct_hash_equal struct NamedColimit <: LimitAlgorithm end 


# Colimit Implementations 
#########################

""" 
Most common representation of the result of a limit computation: a limit cone
"""
@struct_hash_equal struct ColimitCocone <: ColimitImpl
  cocone::Multicospan
end

""" Default colimit for a multicospan """
Colimit(dia::Diagram, c::Multicospan) = Colimit(dia, ColimitCocone(c))

Colimit(dia::Diagram, c::Cospan) = Colimit(dia, Multicospan(c))

# Composite colimit
#------------------

""" Colimit of general diagram computed by coproduct and projection """
@struct_hash_equal struct CompositeColimit{Hom} <: ColimitImpl
  cocone::Multicospan
  coprod::Colimit
  proj::Hom 
end


# Composite pushout 
#------------------

""" Pushout formed as composite of coproduct and equalizer.

See also: [`CompositePullback`](@ref).
"""
struct CompositePushout <: ColimitImpl
  cocone::Multicospan
  coprod::Colimit
  coeq::Colimit
end

function colimit(span::Multispan, m::Category, ::ComposeCoproductCoequalizer)
  coprod = coproduct(feet(span), m)
  (π,) = coeq = coequalizer(map(compose[getvalue(m)], legs(span), legs(coprod)), m)
  cocone = Multicospan(map(ι -> compose(m, ι,π), legs(coprod)))
  Colimit(Diagram(span, m), CompositePushout(cocone, coprod, coeq))
end

function _universal(::Multispan, ::Category, lim::CompositePushout, 
                  cone::Multicospan)
  factorize(lim.coeq, universal(lim.coprod, cone))
end


# Singleton
#----------

""" 
Special case when diagram is a singleton
"""
@struct_hash_equal struct SingletonColimit{Ob,Hom} <: ColimitImpl
  ob::Ob
  i::Hom
  function SingletonColimit(d::SingletonDiagram, m::Category)
    o = only(objects(d))
    i = id(m, o)
    new{typeof(o),typeof(i)}(o, i)
  end
end

ob(s::SingletonColimit) = s.ob

legs(s::SingletonColimit) = [s.i]

cocone(s::SingletonColimit)  = Multicospan(ob(s), legs(s))

"""
In *any* category, we know how to construct the limit of a singleton diagram.
"""
function colimit(d::SingletonDiagram, m::Category, ::DefaultAlg) 
  SingletonColimit(d, m)
  Colimit(Diagram(d, m), SingletonColimit(d, m))
end

 _universal(::Multispan, ::Category, lim::SingletonColimit, 
            cocone::Multicospan)  = only(cocone)

# Generic colimits
####################

""" Colimit of TypeCat determined by dispatching on its implementation """
colimit(d, c::TypeCat, alg) = colimit(d, getvalue(c), alg)

colimit(d::Diagram; alg=DefaultAlg()) = colimit(getvalue(d), getvalue(getcategory(d)), alg)

colimit(d::FreeDiagram{Ob,Hom}, m::Category; alg=DefaultAlg()) where {Ob,Hom} = 
  colimit(BipartiteFreeDiagram(d; colimit=true), m, alg)

colimit(d::FinDomFunctor; alg=DefaultAlg(), kw...) = 
  colimit(FreeDiagram(d), codom(d); alg, kw...)

proj(coeq::Colimit) = only(legs(coeq))

coproj1(colim::Colimit) = let (l,_) = legs(colim); l end

coproj2(colim::Colimit) = let (_,l) = legs(colim); l end


# Named colimits
##################

initial(m::Category; alg=DefaultAlg()) = colimit(Diagram(m); alg)

coproduct(xs::AbstractVector, model::Category; alg=DefaultAlg()) = 
  colimit(DiscreteDiagram(xs), model, alg)


coequalizer(f, g, model::Category; alg=DefaultAlg()) = coequalizer([f,g], model; alg)

coequalizer(xs::AbstractVector, model::Category; alg=DefaultAlg()) = 
  colimit(ParallelMorphisms(xs), model, alg)


pushout(fs::AbstractVector, model::Category; alg=DefaultAlg()) = 
  colimit(Multispan(fs), model, alg)

pushout(f,g, model::Category; alg=DefaultAlg()) = 
  colimit(Multispan([f,g]), model, alg)


# Dispatch on Categories
########################

""" Universal dispatches on the implementation of a Category """
_universal(d::DiagramImpl, c::Category, ci::ColimitImpl, csp::Multicospan) = 
  _universal(d, getvalue(c), ci, csp)

  """ Universal dispatches on the implementation of a TypeCat """
_universal(d::DiagramImpl, c::TypeCat, ci::ColimitImpl, csp::Multicospan) = 
  _universal(d, getvalue(c), ci, csp)

colimit(d::DiagramImpl, c::Category, alg; kw...) = colimit(d, getvalue(c), alg; kw...)

colimit(d::DiagramImpl, c::TypeCat, alg; kw...) = colimit(d, getvalue(c), alg; kw...)
  

# Universal interface
#####################


"""
Apply the universal property of a colimit to a multicospan

Optionally validate the cospan.
"""
function universal(c::Colimit, x::Multicospan; check=false)
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

universal(c::Colimit, x::Cospan; check=false) = universal(c, Multicospan(x); check)



# Named universal maps 
######################

function create(l::Colimit, x)
  getvalue(l.diag) isa EmptyDiagram || error(
    "Can only call `create` on EmptyDiagram colimits")
  universal(l, Multicospan(x, homtype(l)[]))
end


create(x, mod::Category) = create(initial(mod), x)

function factorize(colim::Colimit, h)
  getvalue(colim.diag) isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(colim, Multicospan([h]))
end


""" Copairing of morphisms: universal property of coproducts/pushouts.

To implement for coproducts of type `T`, define the method
`universal(::BinaryCoproduct{T}, ::Cospan{T})` and/or
`universal(::Coproduct{T}, ::Multicospan{T})` and similarly for pushouts.
"""
copair(f, g, m::Category) = copair([f,g], m)

copair(fs::AbstractVector,m::Category)  = 
  copair(coproduct(codom.(fs), m), fs)

copair(colim::Colimit, fs::AbstractVector)  =
  universal(colim, Multicospan(fs))

copair(lim::Colimit, f1::T,f2::T) where {T} = 
  copair(lim, [f1, f2])

# Monoidal 
##########


""" Define cocartesian monoidal structure using colimits.

Implements an instance of [`ThCocartesianCategory`](@ref) assuming that finite
coproducts have been implemented following the colimits interface.
"""
struct CocartesianMonoidal{Ob,Hom} <: Model{Tuple{Ob,Hom}} 
  cat::Category
  CocartesianMonoidal(c::Category) = new{obtype(c), homtype(c)}(c)
end

getvalue(c::CocartesianMonoidal) = c.cat


@instance ThCocartesianCategory{Ob, Hom} [model::CocartesianMonoidal{Ob,Hom}
                                         ] where {Ob,Hom} begin
  @import Ob, Hom, dom, codom, compose, ⋅, →, id, mzero, copair

  oplus(A::Ob, B::Ob) = ob(coproduct([A, B], getvalue(model)))

  function oplus(f::Hom, g::Hom)
    C = getvalue(model)
    ι1, ι2 = coproduct([codom(f), codom(g)], C)
    copair(coproduct([dom(f), dom(g)], C), compose(C, f,ι1), compose(C, g,ι2))
  end

  function swap(A::Ob, B::Ob)
    AB = coproduct([A, B], getvalue(model))
    BA = coproduct([B, A], getvalue(model))
    copair(AB, coproj2(BA), coproj1(BA))
  end

  plus(A::Ob) = copair(id(A),id(A), getvalue(model))
  zero(A::Ob) = create(A, getvalue(model))
  coproj1(A::Ob, B::Ob) = coproj1(coproduct([A, B], getvalue(model)))
  coproj2(A::Ob, B::Ob) = coproj2(coproduct([A, B], getvalue(model)))
end

oplus(m::WithModel{CocartesianMonoidal{Ob,Hom}}, As::AbstractVector{<:Ob}
     ) where {Ob,Hom} = ob(coproduct(As, getvalue(getvalue(m))))
function oplus(m::WithModel{CocartesianMonoidal{Ob,Hom}}, 
               fs::AbstractVector{<:Hom}) where {Ob,Hom}
  C = getvalue(getvalue(m))
  ⊔ = coproduct(map(dom, fs), C)
  ⊔′ = coproduct(map(codom, fs), C)
  copair(⊔, map((x,y)->compose(C,x,y), fs, legs(⊔′)))
end

⊕(m::WithModel{CocartesianMonoidal{Ob,Hom}}, xs::AbstractVector{<:Ob}) where {Ob,Hom} = oplus(m, xs...)

⊕(m::WithModel{CocartesianMonoidal{Ob,Hom}}, xs::AbstractVector{<:Hom}) where {Ob,Hom} = oplus(m, xs...)

mzero(m::WithModel{CocartesianMonoidal{Ob,Hom}}) where {Ob,Hom} = 
  ob(initial(getvalue(getvalue(m))))


end # module
