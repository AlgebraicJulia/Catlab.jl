export Category, Cat, dom, codom, compose, id, obtype, homtype, ob_set, hom_set,
       ThCategoryExplicitSets, ThCategoryWithMonicsEpics, ThCategory, AbsCat, validate, ThConcreteCategory, ob_map, hom_map, lift, ConcreteCategory

using StructEquality

using GATlab
using GATlab.Stdlib: ThCategory

import ....Theories: dom, codom, compose, id 
using ....BasicSets: SetOb
import ....BasicSets: is_monic, is_epic, app

# Theory of Categories with explicit sets
#########################################

"""
A category may have ob and hom sets more specific than Julia types, so we 
extend the interface to require explicitly providing these sets.
"""
@theory ThCategoryExplicitSets <: ThCategory begin
  Set′::TYPE{SetOb}
  ob_set()::Set′
  hom_set()::Set′
end

"""
A (possibly) large category with ob/hom given by SetObs with element types
Ob/Hom.
"""
ThCategoryExplicitSets.Meta.@wrapper Category

""" Coerce something to a category, no-op on actual categories """
Category(c::Category) = c 

# Should this be worked into the constructor somehow? 
# User-provided validation unary operation?
function validate(c::Category) 
  O, H = eltype(ob_set(c)), eltype(hom_set(c))
  ObT, HomT = impl_type(c, :Ob), impl_type(c, :Hom)
  O == ObT || error("Inconsistent ob type $O ≠ $ObT")
  H == HomT || error("Inconsistent hom type: $H ≠ $HomT")
end


""" Alias for [`Category`](@ref). """
const Cat = Category

# unary composition
compose(::Cat, f) = f 

# n-ary composition
compose(c::Cat, f, g, h, fs...) = reduce(compose[getvalue(c)], [f,g,h, fs...])

coerce_set(T::Type, ::Nothing) = SetOb(T)

coerce_set(T::Type, s::SetOb) = 
  eltype(s) == T ? s : error("Bad eltype $s ≠ $T")

Base.show(io::IO, m::Cat) = Base.show(io, getvalue(m))

obtype(c::Category)::Type = eltype(ob_set(c))

homtype(c::Category)::Type = eltype(hom_set(c))

##############
# Extensions # 
##############

# Monos/Epis
############

"""
A category with a decision procedure for telling whether a given morphism is a 
monic and/or an epic.
"""
@theory ThCategoryWithMonicsEpics <: ThCategoryExplicitSets begin
  Bool′::TYPE{Bool}
  is_monic(f::Hom(a::Ob,b::Ob))::Bool′
  is_epic(f::Hom(a::Ob,b::Ob))::Bool′
end

@model_method is_iso

is_iso(m::WithModel, α) = is_monic(m, α) && is_epic(m, α)

# Concrete categories
#####################

"""
A concrete category is a category with a faithful functor into Set.

Faithfulness means is a unique Hom (if any) lying over a given function in Set,
given a choice of domain and codomain.
"""
@theory ThConcreteCategory <: ThCategory begin
  FSet::TYPE{AbsSet}
  FFun::TYPE{AbstractFunction}
  ob_map(a::Ob)::FSet
  hom_map(f::Hom(a,b))::FFun ⊣ [(a,b)::Ob]
  lift(f::FFun, a::Ob, b::Ob)::Hom(a,b) # faithfulness

  lift(hom_map(f), a, b) == f ⊣ [(a,b)::Ob, f::Hom(a,b)]
end

ThConcreteCategory.Meta.@wrapper ConcreteCategory
