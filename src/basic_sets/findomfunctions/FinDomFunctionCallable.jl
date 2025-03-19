module CallableFinDomFn 

export FinDomFunctionCallable

using StructEquality

using GATlab

using ..SetFunctions: SetFunction, dom, codom, SetOb, show_domains
using ...FinSets: FinSet, FinSetInt
using ..FinDomFunctions: FinFunction, ThFinDomFunction, FinDomFunction′
import ..FinDomFunctions:  FinDomFunction
using .ThFinDomFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.
"""
@struct_hash_equal struct FinDomFunctionCallable{D,C}
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::FinSet
  codom::SetOb
  function FinDomFunctionCallable(f, dom::FinSet, codom::SetOb) 
    !isempty(methods(f)) || error("$f must be callable")
    new{eltype(dom), eltype(codom)}(f, dom, codom)
  end
end

GATlab.getvalue(s::FinDomFunctionCallable) = s.func

function Base.show(io::IO, f::FinDomFunctionCallable) 
  print(io, "FinDomFunction")
  print(io, "($(nameof(f.func)), ")
  show_domains(io, FinDomFunction(f))
  print(io, ")")
end

# FinFunction implementation
############################

@instance ThFinDomFunction{D,C} [model::FinDomFunctionCallable{D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::SetOb = model.codom

  app(i::D)::C = getvalue(model)(i)

  # precompose(f::FinFunction)::FinDomFunction′ = precompose(model, f)

  postcompose(f::SetFunction)::FinDomFunction′ =
    FinFunction(i -> f(app[model](i)), model.dom, codom(f)) 

end

# Default constructors 
######################

function FinDomFunction(f::Function, d::FinSet, c::SetOb) 
  FinDomFunction(FinDomFunctionCallable(f, d, c))
end

end # module
