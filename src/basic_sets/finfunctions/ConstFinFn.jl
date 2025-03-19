module ConstFinFn 

export ConstantFinFunction

using StructEquality

using GATlab
import GATlab: getvalue

using ...FinSets, ..FinFunctions
import ..FinFunctions: FinFunction, FinFunction′
import ...SetFunctions: ConstantFunction

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFinFunction{D,C}
  value::Any
  dom::FinSet
  codom::FinSet
  function ConstantFinFunction(v, d::FinSet, c::FinSet)
    v ∈ c || error("Value $v must be element of codom $c")
    new{eltype(d),eltype(c)}(v, d, c)
  end
end


ConstantFinFunction(value::T, dom::FinSet) where T = 
  ConstantFinFunction(value, dom, FinSet(T))

ConstantFunction(v, d::FinSet, c::FinSet) = ConstantFinFunction(v, d, c)
ConstantFunction(value, dom::FinSet) = ConstantFinFunction(value, dom)


getvalue(c::ConstantFinFunction) = c.value

# FinFunction implementation
############################

@instance ThFinFunction{D,C} [model::ConstantFinFunction{D,C}] where {D,C} begin

  dom()::FinSet = model.dom
  
  codom()::FinSet = model.codom

  app(::D)::C = getvalue(model)

  postcompose(f::FinFunction′)::FinFunction′ = FinFunction(
    ConstantFinFunction(f(getvalue(model)), model.dom, codom(f)))

end

end # module
