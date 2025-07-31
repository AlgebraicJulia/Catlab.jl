module RestrictFunctions 

export RestrictFunction

using StructEquality

using GATlab

using ..BasicSets: SetFunction, AbsSet, SetOb, FinSet, ThFinDomFunction, 
                   ThSetFunction, ThFinFunction, FinFunction, FinFunction′, FinDomFunction′, 
                   SetFunction′, show_domains, AbstractFunction
using .ThFinFunction


""" Restrict a function along a subset of its codomain

We can manually check in the case of a function with finite domain, but 
in the case of an infinite domain we must take it on faith that the 
provided set is actually a subset.

To restrict along a subset of the domain, precompose with a `InclFunction`.

The minimal codom this will work for is the `ImgSet` of the function.
"""
@struct_hash_equal struct RestrictFunction{D<:AbsSet,CD<:AbsSet,DT,CDT}
  value::Any
  dom::D
  codom::CD
  function RestrictFunction(v::AbstractFunction, cd)
    cd = isnothing(cd) ? typeof(codom(v))(ImgSet(v)) : cd
    d = dom(v)
    new{typeof(d),typeof(cd),eltype(d),eltype(cd)}(v, d, cd)
  end
end

GATlab.getvalue(c::RestrictFunction) = c.value

# SetFunction implementation
############################

@instance ThSetFunction{D,C} [model::RestrictFunction{SetOb,SetOb,D,C}] where {D,C} begin

  dom()::SetOb = model.dom
  
  codom()::SetOb = model.codom

  app(v::D)::C = app(getvalue(model), v)

  postcompose(f::SetFunction′)::SetFunction′ = postcompose(getvalue(model), f)

end

@instance ThFinFunction{D,C} [model::RestrictFunction{FinSet,FinSet,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::FinSet = model.codom

  app(v::D)::C = app(getvalue(model), v)

  postcompose(f::FinFunction′)::FinFunction′ = postcompose(getvalue(model), f)

end


@instance ThFinDomFunction{D,C} [model::RestrictFunction{FinSet,SetOb,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::FinSet = model.codom

  app(v::D)::C = app(getvalue(model), v)

  postcompose(f::SetFunction′)::FinDomFunction′ = 
    postcompose(getvalue(model), f)

end


end # module
