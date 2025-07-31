module ConstFn 

export ConstantFunction

using StructEquality

using GATlab


using ..BasicSets: SetFunction, AbsSet,SetOb, FinSet, ThFinDomFunction, ThSetFunction, ThFinFunction, FinFunction′, FinDomFunction′, SetFunction′, show_domains
import ..BasicSets:  FinFunction, FinDomFunction, SetFunction, is_indexed
using .ThFinFunction


""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction{DT<:AbsSet,CT<:AbsSet,D,C}
  value::Any
  dom::DT
  codom::CT
  function ConstantFunction(v, d::DT, c::CT) where {DT<:AbsSet,CT<:AbsSet}
    v ∈ c || error("Value $v must be element of codom $c")
    new{DT,CT,eltype(d),eltype(c)}(v, d, c)
  end
end

ConstantFunction(value::T, dom::SetOb) where T = 
  ConstantFunction(value, dom, SetOb(T))

GATlab.getvalue(c::ConstantFunction) = c.value

# SetFunction implementation
############################

@instance ThSetFunction{D,C} [model::ConstantFunction{SetOb,SetOb,D,C}] where {D,C} begin

  dom()::SetOb = model.dom
  
  codom()::SetOb = model.codom

  app(::D)::C = getvalue(model)

  postcompose(f::SetFunction′)::SetFunction′ = SetFunction(
    ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end

@instance ThFinFunction{D,C} [model::ConstantFunction{FinSet,FinSet,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::FinSet = model.codom

  app(::D)::C = getvalue(model)

  postcompose(f::FinFunction′)::FinFunction′ = FinFunction(
    ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end


@instance ThFinDomFunction{D,C} [model::ConstantFunction{FinSet,SetOb,D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::SetOb = model.codom

  app(::D)::C = getvalue(model)

  postcompose(f::SetFunction′)::FinDomFunction′ = FinDomFunction(
    ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end


end # module
