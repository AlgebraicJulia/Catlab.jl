
# Predicated function
#--------------------

""" 
Wrapper around `SetFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFunction <: SetFunctionImpl 
  val::SetFunction
end

getvalue(p::PredicatedFunction) = p.val

@instance ThSetFunction{Any, SetOb, SetFunction} [model::PredicatedFunction] begin
  dom()::SetOb = dom(getvalue(model))
  codom()::SetOb = codom(getvalue(model))
  function app(i::Any)::Any
    f = getvalue(model)
    d, c = dom(f), codom(f)
    getvalue(d) isa PredicatedSet && i ∉ d && error("Bad domain input")
    v = f(i)
    getvalue(c) isa PredicatedSet && v ∉ c && error("Bad codomain output")
    v
  end
  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(PredicatedFunction(i -> f(model.func(i)), dom[model](model), codom[model](f)))
end
