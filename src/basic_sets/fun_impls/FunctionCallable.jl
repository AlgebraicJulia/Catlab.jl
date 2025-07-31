module CallableFn 

export CallableFunction

using StructEquality

using GATlab

using ..BasicSets: SetFunction, AbsSet,SetOb, FinSet, ThFinDomFunction, 
  ThSetFunction, ThFinFunction, FinFunction′, FinDomFunction′, SetFunction′,
  show_domains, AbstractFunction, PredicatedSet
import ..BasicSets:  FinFunction, FinDomFunction, SetFunction, is_indexed
using .ThFinFunction

# Callable 
#---------

""" Function in **Set** defined by a callable Julia object.

If either domain or codomain is a PredicatedSet, then calling the function 
involves extra checks to make sure the input / output are truly in the domain
and codomain respectively (throwing runtime error if not).
"""
@struct_hash_equal struct CallableFunction{DT<:AbsSet,CT<:AbsSet,D,C}
  func::Any   # usually a `Function` but can be any Julia callable.
  dom::DT
  codom::CT
  predicated_dom::Bool
  predicated_codom::Bool
  # TODO switch check to false by default
  function CallableFunction(f, dom::DT, codom::CT; check=true)  where {DT<:AbsSet,CT<:AbsSet}
    !isempty(methods(f)) || error("$f must be callable")
    if check && DT == FinSet  
      dom_elems = collect(dom)
      for d in dom_elems 
        f(d) isa eltype(codom) || error("Bad: $f $d $(f(d)) is not $(eltype(codom)) ")
      end
    end
    pd, pcd = [getvalue(s) isa PredicatedSet for s in [dom, codom]]
    new{DT,CT, eltype(dom), eltype(codom)}(f, dom, codom, pd, pcd)
  end
end

GATlab.getvalue(s::CallableFunction) = s.func

function Base.show(io::IO, f::CallableFunction) 
 ty =  if dom[f]() isa FinSet
    codom[f]() isa FinSet ? "Fin" : "FinDom"
 else
  "Set" 
 end
  print(io, "$(ty)Function")
  print(io, "($(nameof(getvalue(f))), ")
  show_domains(io, f)
  print(io, ")")
end


""" 
Wrapper around `SetFunction` that checks inputs/outputs are compatible with 
(co)domain predicates, if any.
"""
@struct_hash_equal struct PredicatedFunction{F<:AbstractFunction,D,C}
  val::F
  PredicatedFunction(f::F) where F<:AbstractFunction = 
    new{F,impl_type(f, :Dom), impl_type(f, :Cod)}(f)
end

GATlab.getvalue(p::PredicatedFunction) = p.val


# FinFunction implementation
############################

function fun_app(model::CallableFunction{<:Any,<:Any,D,C}, i::D)::C where {D,C}
  f = getvalue(model)
  d, c = model.dom, model.codom
  model.predicated_dom && i ∉ d && error("Bad domain input $i ∉ $d")
  v = f(i)
  model.predicated_codom && v ∉ c && error("Bad codomain output $v ∉ $c ")
  v
end



@instance ThFinFunction{D,C} [model::CallableFunction{FinSet,FinSet,D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::FinSet = model.codom

  app(i::D)::C = fun_app(model, i)

  postcompose(f::FinFunction′)::FinFunction′ =
    FinFunction(i -> f(app[model](i)), model.dom, codom(f)) 

end

@instance ThFinDomFunction{D,C} [model::CallableFunction{FinSet,SetOb,D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::SetOb = model.codom

  app(i::D)::C = fun_app(model, i)

  postcompose(f::SetFunction)::FinDomFunction′ =
    FinDomFunction(i -> f(app[model](i)), model.dom, codom(f)) 

end

@instance ThSetFunction{D,C} [model::CallableFunction{SetOb,CD,D,C}] where {D,C,CD<:AbsSet} begin

  dom()::SetOb = model.dom

  codom()::CD = model.codom

  app(i::D)::C = fun_app(model, i)

  postcompose(f::SetFunction′)::SetFunction′ =
   SetFunction(i -> f(app[model](i)), model.dom, codom(f)) 

end

# Default constructors 
######################

FinFunction(f::Function, d::FinSet, c::FinSet) =
  CallableFunction(f, d, c) |> FinFunction

FinDomFunction(f::Function, d::FinSet, c::SetOb) =
  CallableFunction(f, d, c)  |> FinDomFunction

SetFunction(f::Function, d::SetOb, c::AbsSet) =
  CallableFunction(f, d, c)  |> SetFunction

end # module
