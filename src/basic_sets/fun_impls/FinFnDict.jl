module FinFnDict 

export FinFunctionDict

using StructEquality

using GATlab

using ..BasicSets: SetFunction, AbsSet,SetOb, FinSet, ThFinDomFunction, ThFinFunction
using ..FinFunctions:  FinFunction′
using ..FinDomFunctions: FinDomFunction′
import ..BasicSets:  FinFunction, FinDomFunction
using .ThFinDomFunction

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict{S<:AbsSet,D,C}
  val::Dict
  dom::FinSet
  codom::S
  function FinFunctionDict(val::Dict, dom::FinSet, codom::S) where S<:AbsSet
    for e in dom 
      haskey(val, e) || error("Missing key $e ∈ $dom from $val")
    end
    new{S, eltype(dom),eltype(codom)}(val, dom, codom)
  end
end

""" Default assumed domain """
FinFunctionDict(val::Dict, codom::FinSet) = 
  FinFunctionDict(val, FinSet(Set(collect(keys(val)))), codom)


GATlab.getvalue(f::FinFunctionDict) = f.val

function Base.show(io::IO, f::FinFunctionDict)
  print(io, "FinFunction($(getvalue(f)), ")
  print(io, f.codom)
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThFinFunction{D,C} [model::FinFunctionDict{FinSet, D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::FinSet = model.codom

  app(i::D)::C = getvalue(model)[i]
  
  function postcompose(g::FinFunction′)::FinFunction 
    FinFunction(
      FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), model.dom, codom(g)))
  end
end

@instance ThFinDomFunction{D,C} [model::FinFunctionDict{SetOb, D,C}
                                ] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::SetOb = model.codom

  app(i::D)::C = getvalue(model)[i]
  
  function postcompose(g::SetFunction)::Union{FinFunction′, FinDomFunction′}
    FF = codom(g) isa SetOb ? FinDomFunction : FinFunction
    FF(Dict(k => g(v) for (k,v) in getvalue(model)), model.dom, codom(g))
  end
end

  
""" Default `FinFunction` from a `AbstractDict`"""
FinFunction(f::AbstractDict) = FinFunction(f, FinSet(Set(values(f))))

""" Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, cod::FinSet) = 
  FinFunction(FinFunctionDict(f, cod))

  """ Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, dom::FinSet, cod::FinSet) = 
  FinFunction(FinFunctionDict(f, dom, cod))


""" Default `FinFunction` from a `AbstractDict`"""
FinDomFunction(f::AbstractDict) = FinDomFunction(f, FinSet(Set(keys(f))), FinSet(Set(values(f))))

# TODO IndexedFinDomFunctionDict
""" Default `FinDomFunction` from a `AbstractDict` and codom"""
FinDomFunction(f::AbstractDict, cod::SetOb; index=false) = 
  FinDomFunction(FinFunctionDict(f, FinSet(Set(keys(f))), cod))

  """ Default `FinDomFunction` from a `AbstractDict` and codom"""
FinDomFunction(f::AbstractDict, dom::FinSet, cod::SetOb) = 
  FinDomFunction(FinFunctionDict(f, dom, cod))
  
end # module
