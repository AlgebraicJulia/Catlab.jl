""" 2-category of categories, functors, and natural transformations.

Categories in mathematics appear in the large, often as categories of sets with
extra structure, and in the small, as algebraic structures that generalize
groups, monoids, preorders, and graphs. This division manifests in Catlab as
well. Large categories (in spirit, if not in the [technical
sense](https://ncatlab.org/nlab/show/large+category)) occur throughout Catlab as
`@instance`s of the theory of categories. For computational reasons, small
categories are usually presented by generators and relations.

This module provides a minimal interface to accomodate both situations. Category
instances are supported through the wrapper type [`TypeCat`](@ref). Finitely
presented categories are provided by another module, [`FinCats`](@ref).
"""
module Categories
export Category, Cat, dom, codom, compose, id, obtype, homtype, ob_set, hom_set

using StructEquality
using Reexport

using GATlab
import GATlab: getvalue

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

""" Subtypes of CatImpl ought be instances of `ThCategoryExplicitSets` """
abstract type CatImpl{Ob,Hom} <: Model{Tuple{Ob,Hom,AbsSet}} end

# Wrapper type for models of ThCategoryExplicitSets
###################################################
"""
A (possibly) large category with ob/hom given by AbsSets with element types
Ob/Hom. It is a wrapper around some implementation of the theory of categories.
"""
@struct_hash_equal struct Category
  mod::CatImpl
  function Category(m::CatImpl{ObT,HomT}) where {ObT,HomT}
    implements(m, ThCategoryExplicitSets)|| error("Bad model $m")
    O = ThCategoryExplicitSets.ob_set[m]()
    H = ThCategoryExplicitSets.hom_set[m]()
    eltype(O) == ObT || error("Bad ob type")
    eltype(H) == HomT || error("Bad ob type")
    new(m)
  end
end 

getvalue(c::Category) = c.mod

""" Alias for [`Category`](@ref). """
const Cat = Category

# Access model methods
#---------------------

dom(c::Cat, f) = dom[getvalue(c)](f)

codom(c::Cat, f) = codom[getvalue(c)](f)

id(c::Cat, x) = id[getvalue(c)](x)

compose(::Cat) = error("Cannot compose empty sequence of morphisms") 

compose(::Cat, f) = f 

compose(c::Cat, fs...) = reduce(compose[getvalue(c)], fs)

ob_set(c::Cat) = ob_set[getvalue(c)]()

hom_set(c::Cat) = hom_set[getvalue(c)]()

# Other methods 
#--------------

coerce_set(T::Type, ::Nothing) = SetOb(T)

coerce_set(T::Type, s::AbsSet) = eltype(s) == T ? s : error("Bad eltype $s ≠ $T")

Base.show(io::IO, m::Cat) = Base.show(io, getvalue(m))

obtype(c)::Type = eltype(ob_set(c))

homtype(c)::Type = eltype(hom_set(c))

# Implementations
#----------------

include("CatImpls/TypeCats.jl")
include("CatImpls/OpCats.jl")
include("CatImpls/TrivialCats.jl")
include("CatImpls/FinCats.jl")

@reexport using .TypeCats
@reexport using .OpCats
@reexport using .TrivialCats
@reexport using .FinCats


end # module
