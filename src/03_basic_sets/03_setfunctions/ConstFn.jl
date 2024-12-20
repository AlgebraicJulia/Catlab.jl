module ConstFn 

export ConstantFunction

using StructEquality

using GATlab
import GATlab: getvalue

using ..Sets: AbsSet, SetOb
using ..SetFunctions: ThSetFunction, codom
import ..SetFunctions: SetFunction

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction{D<:AbsSet,C<:AbsSet}
  value::Any
  dom::D
  codom::C
  function ConstantFunction(v, d::D, c::C) where {D<:AbsSet,C<:AbsSet}
    v ∈ c || error("Value $v must be element of codom $c")
    new{D,C}(v, d, c)
  end
end

ConstantFunction(value::T, dom::AbsSet) where T = 
  ConstantFunction(value, dom, SetOb(T))

# Accesssor 
###########

getvalue(c::ConstantFunction) = c.value

# SetFunction implementation
############################

@instance ThSetFunction{Any, SetFunction, D, C
                       } [model::ConstantFunction{D,C}] where {D,C} begin

  dom()::D = model.dom
  
  codom()::C = model.codom

  app(x::Any)::Any = getvalue(model)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end

end # module
