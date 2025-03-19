module CallableFinFn 

export FinFunctionCallable

using StructEquality

using GATlab

using ...FinSets
using ...SetFunctions: show_domains
import ..FinFunctions: FinFunction, FinFunction′, ThFinFunction
using ..PredFinFn: PredicatedFinFunction
using .ThFinFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct FinFunctionCallable{D,C}
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::FinSet
  codom::FinSet
  function FinFunctionCallable(f, dom::FinSet, codom::FinSet) 
    !isempty(methods(f)) || error("$f must be callable")
    new{eltype(dom), eltype(codom)}(f, dom, codom)
  end
end

GATlab.getvalue(s::FinFunctionCallable) = s.func

function Base.show(io::IO, f::FinFunctionCallable) 
  print(io, "FinFunction")
  print(io, "($(nameof(f.func)), ")
  show_domains(io, FinFunction(f))
  print(io, ")")
end

# FinFunction implementation
############################

@instance ThFinFunction{D,C} [model::FinFunctionCallable{D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::FinSet = model.codom

  app(i::D)::C = getvalue(model)(i)

  postcompose(f::FinFunction′)::FinFunction′ =
    FinFunction(i -> f(app[model](i)), model.dom, codom(f)) 

end

# Default constructors 
######################

function FinFunction(f::Function, d::FinSet, c::FinSet) 
  s = FinFunctionCallable(f, d, c)  |> FinFunction
  pred = getvalue(d) isa PredicatedFinSet || getvalue(c) isa PredicatedFinSet
  pred ? FinFunction(PredicatedFinFunction(s)) : s
end

end # module
