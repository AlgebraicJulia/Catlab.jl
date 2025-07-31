""" Algebra of subobjects in a category.

This module defines the interface for subobjects as well as some generic
algorithm for computing subobjects using limits and colimits. Concrete instances
such as subsets (subobjects in Set or FinSet) and sub-C-sets (subobjects in
C-Set) are defined elsewhere.
"""
module Subobjects
export Subobject, SubobjectHom, ob, hom, SubOpCatLimits,
  ThSubobjectLattice, ThSubobjectHeytingAlgebra, ThSubobjectBiHeytingAlgebra,
  meet, ∧, join, ∨, top, ⊤, bottom, ⊥,
  implies, ⟹, subtract, \, negate, ¬, non, ~

import Base: \, ~
using StructEquality
using StaticArrays: SVector

using GATlab
import ....Theories: ob, hom, meet, ∧, join, ∨, top, ⊤, bottom, ⊥
using ....Theories, ..LimitsColimits
using ..FreeDiagrams: legs
using ..Categories: Category

# Theories
##########

""" Theory of lattice of subobjects in a coherent category, such as a pretopos.

The axioms are omitted since this theory is the same as the theory
[`Catlab.Theories.ThAlgebraicLattice`](@ref) except that the lattice elements
are dependent on another type. In fact, if we supported GAT morphisms, it should
be possible to define a projection morphism of GATs from `ThSubobjectLattice` to
`ThAlgebraicLattice` that sends `Ob` to the unit type.
"""
@signature ThSubobjectLattice begin
  Ob::TYPE
  Sub(ob::Ob)::TYPE

  @op begin
    (∧) := meet
    (∨) := join
    (⊤) := top
    (⊥) := bottom
  end

  meet(A::Sub(X), B::Sub(X))::Sub(X) ⊣ [X::Ob]
  join(A::Sub(X), B::Sub(X))::Sub(X) ⊣ [X::Ob]
  top(X::Ob)::Sub(X)
  bottom(X::Ob)::Sub(X)
end

""" Theory of Heyting algebra of subobjects in a Heyting category, such as a
topos.
"""
@signature ThSubobjectHeytingAlgebra <: ThSubobjectLattice begin
  @op begin
    (⟹) := implies
    (¬) := negate
  end

  implies(A::Sub(X), B::Sub(X))::Sub(X) ⊣ [X::Ob]
  negate(A::Sub(X))::Sub(X) ⊣ [X::Ob]
end

""" Theory of bi-Heyting algebra of subobjects in a bi-Heyting topos, such as a
presheaf topos.
"""
@signature ThSubobjectBiHeytingAlgebra <: ThSubobjectHeytingAlgebra begin
  @op begin
    (\) := subtract
    (~) := non
  end

  subtract(A::Sub(X), B::Sub(X))::Sub(X) ⊣ [X::Ob]
  non(A::Sub(X))::Sub(X) ⊣ [X::Ob]
end

# Data types
############

""" Subobject in a category.

By definition, a subobject of an object ``X`` in a category is a monomorphism
into ``X``. This is the default representation of a subobject. Certain
categories may support additional representations. For example, if the category
has a subobject classifier ``Ω``, then subobjects of ``X`` are also morphisms
``X → Ω``.
"""
abstract type Subobject{Ob} end

# Default constructor for subobjects assumes a morphism representation.
Subobject(hom) = SubobjectHom(hom)

@struct_hash_equal struct SubobjectHom{Ob,Hom} <: Subobject{Ob}
  hom::Hom
  SubobjectHom(hom::Hom) where Hom = new{typeof(codom(hom)),Hom}(hom)
end

hom(sub::SubobjectHom) = sub.hom
ob(sub::SubobjectHom) = codom(hom(sub))

# Algorithms
############

"""
Model of `ThSubobjectLattice`, given a category that has pullbacks and pushouts.
"""
struct SubOpCatLimits{Ob,Hom}
  m::Any
  function SubOpCatLimits(m)
    O, H = impl_type.(Ref(m), Ref(ThCategoryWithPushouts), [:Ob, :Hom]) 
    implements(m, ThCategoryWithPushouts) || error("Bad $m: no pushouts")
    implements(m, ThCategoryWithPullbacks) || error("Bad $m: no pullbacks")
    new{O,H}(m)
  end
end 

GATlab.getvalue(s::SubOpCatLimits) = s.m

@instance ThSubobjectLattice{O,SubobjectHom{O,H}} [model::SubOpCatLimits{O,H}
                                             ] where {O,H} begin 
  """ Meet (intersection) of subobjects.
  """
  function meet(A::Subobject{O}, B::Subobject{O})
    As, 𝒞 = [A,B], getvalue(model)
    fs = map(hom, As)
    lim = legs(pullback[𝒞 ](fs))
    Subobject(compose[𝒞](first(lim), first(fs))) # Arbitrarily use first leg.
  end

  """ Join (union) of subobjects.
  """
  function join(A::Subobject{O}, B::Subobject{O})
    As, 𝒞 = [A,B], getvalue(model)
    fs = map(hom, As)
    lim = pullback[𝒞](fs)
    colim = pushout[𝒞](legs(lim)...)
    Subobject(copair[𝒞](colim, fs))
  end

  """ Top (full) subobject.
  """
  top(X) = Subobject(id[getvalue(model)](X))

  """ Bottom (empty) subobject.
  """
  bottom(X) = Subobject(create[getvalue(model)](X))
end

end # module
