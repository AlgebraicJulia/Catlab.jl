module Decorated
using Catlab
using Catlab.Theories
import Catlab.Theories: compose
using Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: legs, apex
using Catlab.CategoricalAlgebra.Categories
import Catlab.CategoricalAlgebra.Categories: do_ob_map, do_hom_map, LargeCatSize
import Catlab.CategoricalAlgebra.Limits: CompositePushout
using Catlab.Sheaves

export AbstractDecorator, functor, laxator, DecoratedCospan, VectCospan,
  CorelationDecorator, FVectPushforward, Vect, SummationProjection,
  glue

"""    AbstractDecorator

An abstract class to overload for define a set of decorations.
"""
abstract type AbstractDecorator end

"""    functor(d::AbstractDecorator)

Get the functor part of the decorator
"""
functor(d::AbstractDecorator) = error("Not Implemented: functor for $(typeof(d))")

"""    laxator(d::AbstractDecorator)

Get the laxator part of the decorator
"""
laxator(d::AbstractDecorator) = error("Not Implemented: laxator for $(typeof(d))")

"""    Decorator

A struct for a decorator functor and a laxator.
"""
struct Decorator{F,L} <: AbstractDecorator
  functor::F
  laxator::L
end

functor(d::Decorator) = d.functor
laxator(d::Decorator) = d.laxator


"""    DecoratedCospan

An abstract class decorated cospans. You need to implement:

1. legs
2. apex
3. decorator
4. decoration
"""
abstract type DecoratedCospan end

decorator(f::DecoratedCospan) = error("Not Implemented: decorator for $(typeof(f))")
legs(f::DecoratedCospan) = error("Not Implemented: legs for $(typeof(f))")
apex(f::DecoratedCospan) = error("Not Implemented: apex for $(typeof(f))")

coequalizer_map(d::CompositePushout) = d.coeq.cocone.legs[1]

"""    glue(F::Decorator, cospan::CompositePushout, decorations::AbstractVector)

Compute the composite system by the decorated cospan construction.
"""
function glue(F::Decorator, cospan::CompositePushout, decorations::AbstractVector)
  πq = coequalizer_map(cospan)
  ϕ = do_hom_map(F.functor, πq)
  ϕ(F.laxator(decorations))
end

function glue(D::Decorator, f::DecoratedCospan, g::DecoratedCospan)
  # this notation is from Fong 2017 https://arxiv.org/abs/1703.09888 page 13.
  # invoke the decorated cospans part to build the composite
  oy = legs(f)[2]
  iy = legs(g)[1]
  p = pushout(oy,iy)
  decorations = [f.decoration, g.decoration]
  composite = glue(D.action, p, decorations)

  # put the new legs on for the interface.
  ix = legs(f)[1]
  oz = legs(g)[2]
  return typeof(f)(composite, Cospan(ix, oz))
end

"""    FactorizationSystem{C}

An abstract type for representing an orthogonal factorization. Examples include:

  1. `EpiMono`
"""
abstract type FactorizationSystem{C<:Category} end

# API for a generic factorization system.
category(::FactorizationSystem{C}) where C = C
epis(fs::FactorizationSystem) = error("Not Implemented: epis for $(typeof(fs))")
monos(fs::FactorizationSystem) = error("Not Implemented: monos for $(typeof(fs))")
factor(em::FactorizationSystem, f) = error("Not Implemented: factor($(typeof(em)),$(typeof(f)))")


struct FinSetEpi <: Category{FinSet, FinFunction, LargeCatSize} end
struct FinSetMono <: Category{FinSet, FinFunction, LargeCatSize} end

"""    EpiMono

The factorization system for the classic epimorphisms (surjective functions) and monomorphisms (injective functions) in Set.
"""
struct EpiMono <: FactorizationSystem{FinSetCat} end

epis(::EpiMono) = FinSetEpi()
monos(::EpiMono) = FinSetMono()
factor(::EpiMono, f::FinFunction) = epi_mono(f)

"""    CorelationDecorator

A struct for what you need for a decorated corelations construction. The fields are:

  1. action: the covariant functor from C to Set (and its laxator)
  2. coaction: the contravariant functor from C^op to Set
  3. factorization: a factorization system on C

"""
struct CorelationDecorator{F,L,R} <: AbstractDecorator
  action::Decorator{F,L}
  coaction::R
  factorization::FactorizationSystem
end

"""    glue(D::CorelationDecorator, f::DecoratedCospan, g::DecoratedCospan)

Compute the composite system by the decorated cospan construction.
"""
function glue(D::CorelationDecorator, f::DecoratedCospan, g::DecoratedCospan)
  # this notation is from Fong 2017 https://arxiv.org/abs/1703.09888 page 13.
  # invoke the decorated cospans part to build the composite
  oy = legs(f)[2]
  iy = legs(g)[1]
  p = pushout(oy,iy)
  decorations = [f.decoration, g.decoration]
  composite = glue(D.action, p, decorations)

  # project onto the image of the outer ports
  ix = legs(f)[1]
  oz = legs(g)[2]
  
  jN = legs(p)[1]
  jM = legs(p)[2]

  coprod2composite = copair(compose(ix, jN), compose(oz, jM))
  _, m = factor(D.factorization, coprod2composite)
  decorator = do_hom_map(D.coaction,m)(composite)
  return decorator
end

"""    FreeVect{T} where T <: Number

The covariant free vector space functor. 
The returned  function f✶ sums over preimages.
"""
FVectPushforward = Functor(identity, # identity on objects
  # specify the pushforward construction
  f->(v->begin
    z = zero(eltype(v))
    map(codom(f)) do i
    sum(v[j] for j in preimage(f,i); init=z)
  end end),
  # covariant functor from FinSetCat to FinVect
  FinSetCat(), FinVect()
)

Vect = Decorator(FVectPushforward, vs -> reduce(vcat, vs))
SummationProjection = CorelationDecorator(Vect, Sheaves.FVectPullback(), EpiMono())

"""    VectCospan

A type to hold cospans decorated by the SummationProjection decorator.
"""
struct VectCospan <: DecoratedCospan
  decoration::AbstractVector
  cospan
end

decorator(::VectCospan) = SummationProjection
legs(f::VectCospan) = legs(f.cospan)
apex(f::VectCospan) = apex(f.cospan)

function Base.show(io::IO, f::VectCospan)
  println(io, "DecoratedCospan begin")
  print(io, "cospan decorator: Free Vector Space Functor")
  print(io, "corelations decorator: SummationProjection")
  println(io, "decoration: $(f.decoration)")
  println(io, "legs: ")
  map(legs(f.cospan)) do l
    println(io, "  $l")
  end
  print(io, "end")
end

end