module CallableFn 

export SetFunctionCallable

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction, SetFunction′
using ..PredFn: PredicatedFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable{D,C}
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::SetOb
  codom::SetOb
  function SetFunctionCallable(f, dom::SetOb, codom::SetOb) 
    !isempty(methods(f)) || error("$f must be callable")
    new{eltype(dom), eltype(codom)}(f, dom, codom)
  end
end

GATlab.getvalue(s::SetFunctionCallable) = s.func

function Base.show(io::IO, f::SetFunctionCallable) 
  print(io, "SetFunction")
  print(io, "($(nameof(f.func)), ")
  show_domains(io, SetFunction(f))
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThSetFunction{D,C} [model::SetFunctionCallable{D,C}] where {D,C} begin

  dom()::SetOb = model.dom

  codom()::SetOb = model.codom

  app(i::D)::C = getvalue(model)(i)

  postcompose(f::SetFunction′)::SetFunction′ = 
    SetFunction(SetFunctionCallable(  
      i -> f(getvalue(model.func)(i)), model.dom, codom(f)))

end

# Default constructors 
######################

function SetFunction(f::Function, d::SetOb, c::SetOb) 
  s = SetFunctionCallable(f, d, c)  |> SetFunction
  pred = getvalue(d) isa PredicatedSet || getvalue(c) isa PredicatedSet
  pred ? SetFunction(PredicatedFunction(s)) : s
end

end # module
