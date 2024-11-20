""" Categories of C-sets and attributed C-sets.
"""
module CSets
export CSetCat, ACSetCat

using Base.Iterators: flatten
using Reexport
using StructEquality

@reexport using ACSets
@reexport using ....ACSetsGATsInterop

using GATlab, CompTime
using ....Theories
using ....Theories: @default_model
import ....Theories: id
using ...Cats, ...BasicSets
import ...Cats: FinDomFunctor
using ..ACSetTransformations, ..ACSetSetInterop



# Category of C-sets
####################

"""
The category of C-Sets has objects which are ACSets with no attributes.
"""
@struct_hash_equal struct CSetCat <: Model{Tuple{ACSet, ACSetTransformation}} end

@instance ThCategory{ACSet, ACSetTransformation} [model::CSetCat] begin

  function Ob(X::ACSet)
    at = attrtypes(acset_schema(X))
    isempty(at) || @fail "Cannot have attribute types $at"
    return X
  end

  function Hom(α::ACSetTransformation, dom::ACSet, codom::ACSet)
    is_natural(α) || @fail "Unnatural transformation"
    α
  end

  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::ACSet) = ACSetTransformation(map(id[SetC()], sets(X)), X, X)

  # Question: Should we incur cost of checking that codom(β) == dom(α)?
  # If either is Loose, return a Loose
  compose(α::ACSetTransformation, β::ACSetTransformation) =
    ACSetTransformation(map(compose[SetC()], components(α), components(β)), dom(α), codom(β))
end


"""
The category of ACSets (and *tight* transformations) has ...
"""
@struct_hash_equal struct ACSetCat <: Model{Tuple{ACSet, ACSetTransformation}} end

@instance ThCategory{ACSet, ACSetTransformation} [model::ACSetCat] begin

  function Ob(X::ACSet)
    at = attrtypes(acset_schema(X))
    isempty(at) || @fail "Cannot have attribute types $at"
    return X
  end

  function Hom(α::ACSetTransformation, dom::ACSet, codom::ACSet)
    is_natural(α) || @fail "Unnatural transformation"
    α
  end

  dom(α::ACSetTransformation) = α.dom
  codom(α::ACSetTransformation) = α.codom

  id(X::ACSet) = ACSetTransformation(map(id[SetC()], sets(X; var=true)), X, X)

  compose(α::ACSetTransformation, β::ACSetTransformation) =
    ACSetTransformation(map(compose[SetC()], components(α), components(β)), dom(α), codom(β))
end

# @cartesian_monoidal_instance ACSet ACSetTransformation ACSetLoose

@cocartesian_monoidal_instance ACSet ACSetTransformation CSetCat

@default_model ThCategory{ACSet, ACSetTransformation} [model::CSetCat]


end # module
