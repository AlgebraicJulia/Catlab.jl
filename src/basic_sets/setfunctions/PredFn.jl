module PredFn 

export PredicatedFunction

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction

""" 
Wrapper around `SetFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFunction 
  val::AbsFunction
end

# Accessor
##########

GATlab.getvalue(p::PredicatedFunction) = p.val

# SetFunction Implementation
############################

@instance ThSetFunction [model::PredicatedFunction] begin

  dom()::AbsSet = dom(getvalue(model))

  codom()::AbsSet = codom(getvalue(model))

  function app(i::Any)::Any
    f = getvalue(model)
    d, c = dom(f), codom(f)
    getvalue(d) isa PredicatedSet && i ∉ d && error("Bad domain input")
    v = f(i)
    getvalue(c) isa PredicatedSet && v ∉ c && error("Bad codomain output")
    v
  end

  postcompose(f::AbsFunction)::AbsFunction = PredicatedFunction(
    i -> f(getvalue(model)(i)), dom[model](model), codom[model](f)) |> SetFunction
end

end # module
