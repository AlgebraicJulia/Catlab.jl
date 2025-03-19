module ConstFn 

export ConstantFunction

using StructEquality

using GATlab
import GATlab: getvalue

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction, SetFunction′

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction{D,C}
  value::Any
  dom::SetOb
  codom::SetOb
  function ConstantFunction(v, d::SetOb, c::SetOb)
    v ∈ c || error("Value $v must be element of codom $c")
    new{eltype(d),eltype(c)}(v, d, c)
  end
end

ConstantFunction(value::T, dom::SetOb) where T = 
  ConstantFunction(value, dom, SetOb(T))

getvalue(c::ConstantFunction) = c.value

# SetFunction implementation
############################

@instance ThSetFunction{D,C} [model::ConstantFunction{D,C}] where {D,C} begin

  dom()::SetOb = model.dom
  
  codom()::SetOb = model.codom

  app(::D)::C = getvalue(model)

  postcompose(f::SetFunction′)::SetFunction′ = SetFunction(
    ConstantFunction(f(getvalue(model)), model.dom, codom(f)))

end

end # module
