module CallableFn 

export SetFunctionCallable

using StructEquality

using GATlab

using ..Sets, ..SetFunctions
import ..SetFunctions: SetFunction
using ..PredFn: PredicatedFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::AbsSet
  codom::AbsSet
  function SetFunctionCallable(f, dom::AbsSet, codom::AbsSet) 
    !isempty(methods(f)) || error("$f must be callable")
    new(f, dom, codom)
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

@instance ThSetFunction [model::SetFunctionCallable] begin

  dom()::AbsSet = model.dom

  codom()::AbsSet = model.codom

  app(i::Any)::Any = getvalue(model)(i)

  postcompose(f::AbsFunction)::AbsFunction = 
    SetFunction(SetFunctionCallable(  
      i -> f(getvalue(model.func)(i)), model.dom, codom(f)))

end

# Default constructors 
######################

function SetFunction(f::Function, d::AbsSet, c::AbsSet) 
  s = SetFunctionCallable(f, d, c)  |> SetFunction
  pred = getvalue(d) isa PredicatedSet || getvalue(c) isa PredicatedSet
  pred ? SetFunction(PredicatedFunction(s)) : s
end

end # module
