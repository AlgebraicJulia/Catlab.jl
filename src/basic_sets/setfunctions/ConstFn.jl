module ConstFn 

export ConstantFunction

using StructEquality

using GATlab
import GATlab: getvalue

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction#{D<:AbsSet,C<:AbsSet}
  value::Any
  dom::AbsSet
  codom::AbsSet
  function ConstantFunction(v, d::AbsSet, c::AbsSet)
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

@instance ThSetFunction [model::ConstantFunction] begin

  dom()::AbsSet = model.dom
  
  codom()::AbsSet = model.codom

  app(::Any)::Any = getvalue(model)

  postcompose(f::AbsFunction)::AbsFunction = 
    SetFunction(ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end

end # module
