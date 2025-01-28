module CallableFn 

export SetFunctionCallable

using StructEquality

using GATlab

using ..Sets: AbsSet, PredicatedSet
using ..SetFunctions: ThSetFunction, show_domains
import ..SetFunctions: SetFunction
using ..PredFn: PredicatedFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct SetFunctionCallable{D<:AbsSet,C<:AbsSet}
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::D
  codom::C
  function SetFunctionCallable(f, dom::D, codom::C) where {D,C}
    !isempty(methods(f)) || error("$f must be callable")
    new{D,C}(f, dom, codom)
  end
end

# Accessors
############

GATlab.getvalue(s::SetFunctionCallable) = s.func

# Other methods 
###############

function Base.show(io::IO, f::SetFunctionCallable) 
  print(io, "SetFunction")
  print(io, "($(nameof(f.func)), ")
  show_domains(io, SetFunction(f))
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThSetFunction{Any, SetFunction, D, C} [model::SetFunctionCallable{D,C}] where {D,C} begin

  dom()::D = model.dom

  codom()::C = model.codom

  app(i::Any)::Any = getvalue(model)(i)

  postcompose(f::SetFunction)::SetFunction = 
    SetFunction(SetFunctionCallable(  
      i -> f(getvalue(model.func)(i)), model.dom, codom(f)))

end


# Default constructors 
######################

SetFunction(f::Function, d::AbsSet, c::AbsSet) = _set_fn(SetFunction, f, d, c)

SetFunction{A,B,C,D}(f::Function, d::AbsSet, c::AbsSet) where {A,B,C,D} = 
  _set_fn(SetFunction{A,B,C,D}, f, d, c)

""" Common code between the above two methods """
function _set_fn(T, f, d, c)
  s = SetFunctionCallable(f, d, c) |> T
  pred = getvalue(d) isa PredicatedSet || getvalue(c) isa PredicatedSet
  pred ? T(PredicatedFunction(s)) : s
end

end # module
