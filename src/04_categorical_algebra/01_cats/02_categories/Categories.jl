export Category, Cat, dom, codom, compose, id, obtype, homtype, ob_set, hom_set,
       ThCategoryExplicitSets

using StructEquality

using GATlab

import ....Theories: dom, codom, compose, id 
using ....BasicSets: AbsSet

# Theory of Categories with explicit sets
#########################################

"""
A category may have ob and hom sets more specific than Julia types, so we 
extend the interface to require explicitly providing these sets.
"""
@theory ThCategoryExplicitSets <: ThCategory begin
  Set′::TYPE
  ob_set()::Set′
  hom_set()::Set′
end

""" Subtyped by wrappers by Cat and FinCat """
abstract type AbsCat end 
"""
A (possibly) large category with ob/hom given by AbsSets with element types
Ob/Hom.
"""
ThCategoryExplicitSets.Meta.@wrapper Category <: AbsCat

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

coerce_set(T::Type, s::AbsSet) = 
  eltype(s) == T ? s : error("Bad eltype $s ≠ $T")

Base.show(io::IO, m::Cat) = Base.show(io, getvalue(m))

obtype(c::Category)::Type = eltype(ob_set(c))

homtype(c::Category)::Type = eltype(hom_set(c))

