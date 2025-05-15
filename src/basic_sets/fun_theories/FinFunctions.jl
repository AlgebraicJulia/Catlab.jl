module FinFunctions 

export FinFunction, FinFunction′, ThFinFunction, preimage, dom, codom, app, postcompose, is_epic

import ACSets.Columns: preimage, Column
using GATlab

using ..FinSets: FinSet
using ..SetFunctions: ThFunctionCore, ThSetFunction
import .ThSetFunction: dom, codom, app, postcompose

# Finite functions
##################
""" This is only subtyped by FinFunction """
abstract type FinFunction′ end 


"""
A FinFunction is anything that can play the role of a morphism in the category 
FinSet. This means we can pick out a dom and codom set, we apply the function
to any domain element to get a codomain element, and we and turn a sequence of 
FinFunctions into a single one. In principle FinFunctions need not know anything
about composition: the composite of any two FinFunctions is a `CompositeFinFunction` 
implementation. However, we often want to simplify a `CompositeFunction` into a 
more compressed form (which would be more efficient if one were repeatedly 
calling the function). So implementations are also required to have a method 
which is used (within `force`) to simplify a `CompositeFunction`. One could 
demand both pre- and post-composition operations, but just one suffices to 

Often, implementations are naturally postcomposed with another function, because 
this allows one to keep the same structure but just update the values. However,
there are _some_ function implementations which do fundamentally change upon 
postcomposition, such as an `IdentityFinFunction`. Also, in the case of  
`ConstantFinFunction`s, one more efficiently represents a postcomposition not by 
mapping over the structure with the same value but by just replacing the
function with another `ConstantFunction`. `postcompose` is only ever called when
using `force` to evaluate a `CompositeFunction`.
"""
@theory ThFinFunction <: ThFunctionCore begin
  Fun′::TYPE{FinFunction′}
  DomSet::TYPE{FinSet}
  CodSet::TYPE{FinSet}
  dom()::DomSet # eltype(dom()) <: Dom
  codom()::CodSet # eltype(codom()) <: Cod
  postcompose(t::Fun′)::Fun′
end

ThFinFunction.Meta.@wrapper FinFunction <: FinFunction′

Base.show(io::IO, f::FinFunction) = show(io, getvalue(f))
(f::FinFunction)(i) = app(f, i)


# These could be made to fail early if ever used in performance-critical areas
"""
Whether something is an epi is a holistic property of a morphism in the context 
of a whole category. Thus an `is_epic` predicate must implicitly interprets 
FinFunctions as morphisms in a category. We naturally choose FinSet.
"""
is_epic(f::FinFunction) = length(codom(f)) == length(Set(values(collect(f))))

# ACSet Interface
#################
FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(Int[c[i] for i in dom], codom)

end # module
