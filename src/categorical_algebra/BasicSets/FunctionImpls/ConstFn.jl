module ConstFn 

export ConstantFunction

using StructEquality

using GATlab
import GATlab: getvalue

using ...Sets: AbsSet, SetOb
using ..SetFunctions: SetFunctionImpl, ThSetFunction, codom
import ..SetFunctions: SetFunction

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction <: SetFunctionImpl
  value::Any
  dom::AbsSet
  codom::AbsSet
  function ConstantFunction(v, d, c)
    v ∈ c || error("Value $v must be element of codom $c")
    new(v, d, c)
  end
end

ConstantFunction(value::T, dom::AbsSet) where T = 
  ConstantFunction(value, dom, SetOb(T))

# Accesssor 
###########

getvalue(c::ConstantFunction) = c.value

# SetFunction implementation
############################

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::ConstantFunction] begin

  dom()::AbsSet = model.dom
  
  codom()::AbsSet = model.codom

  app(x::Any)::Any = getvalue(model)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end

# Default `SetFunction` constructor 
###################################

SetFunction(value, dom::AbsSet) = SetFunction(ConstantFunction(value, dom))

end # module
