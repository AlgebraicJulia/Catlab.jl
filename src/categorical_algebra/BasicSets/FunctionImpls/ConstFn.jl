
# Constant functions
#-------------------

""" Function in **Set** taking a constant value.
"""
@struct_hash_equal struct ConstantFunction <: SetFunctionImpl
  value::Any
  dom::AbsSet
  codom::AbsSet
  function ConstantFunction(v, d, c)
    v ∈ c || error("Value must be in codom")
    new(v, d, c)
  end
end

ConstantFunction(value::T, dom::AbsSet) where T = 
  ConstantFunction(value, dom, SetOb(T))

getvalue(c::ConstantFunction) = c.value

# SetFunction implementation

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::ConstantFunction] begin
  dom()::AbsSet = model.dom
  
  codom()::AbsSet = model.codom

  app(x::Any)::Any = getvalue(model)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(ConstantFunction(f(getvalue(model)), model.dom, codom(f)))
end

# Default constructors 

SetFunction(value, dom::AbsSet) = SetFunction(ConstantFunction(value, dom))