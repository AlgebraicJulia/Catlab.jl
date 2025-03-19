module PredFn 

export PredicatedFunction

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction, SetFunction′

""" 
Wrapper around `SetFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFunction{D,C}
  val::SetFunction
  PredicatedFunction(f::SetFunction) = 
    new{impl_type(f, :Dom), impl_type(f, :Cod)}(f)
end

GATlab.getvalue(p::PredicatedFunction) = p.val

# SetFunction Implementation
############################

@instance ThSetFunction{D,C} [model::PredicatedFunction{D,C}] where {D,C} begin

  dom()::SetOb = dom(getvalue(model))

  codom()::SetOb = codom(getvalue(model))

  function app(i::D)::C
    f = getvalue(model)
    d, c = dom(f), codom(f)
    getvalue(d) isa PredicatedSet && i ∉ d && error("Bad domain input")
    v = f(i)
    getvalue(c) isa PredicatedSet && v ∉ c && error("Bad codomain output")
    v
  end

  postcompose(f::SetFunction′)::SetFunction′ = PredicatedFunction(
    i -> f(getvalue(model)(i)), dom[model](model), codom[model](f)) |> SetFunction
end

end # module
