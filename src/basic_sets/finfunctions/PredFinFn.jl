module PredFinFn 

export PredicatedFinFunction

using StructEquality

using GATlab

using ...Sets, ...SetFunctions
import ..FinFunctions: FinFunction, FinFunction′, ThFinFunction

""" 
Wrapper around `FinFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFinFunction{D,C}
  val::FinFunction
  PredicatedFinFunction(f::FinFunction) = 
    new{impl_type(f, :Dom), impl_type(f, :Cod)}(f)
end

GATlab.getvalue(p::PredicatedFinFunction) = p.val

# FinFunction Implementation
############################

@instance ThFinFunction{D,C} [model::PredicatedFinFunction{D,C}] where {D,C} begin

  dom()::FinSet = dom(getvalue(model))

  codom()::FinSet = codom(getvalue(model))

  function app(i::D)::C
    f = getvalue(model)
    d, c = dom(f), codom(f)
    getvalue(d) isa PredicatedSet && i ∉ d && error("Bad domain input")
    v = f(i)
    getvalue(c) isa PredicatedSet && v ∉ c && error("Bad codomain output")
    v
  end

  postcompose(f::FinFunction′)::FinFunction′ = PredicatedFinFunction(
    i -> f(getvalue(model)(i)), dom[model](model), codom[model](f)) |> FinFunction
end

end # module
