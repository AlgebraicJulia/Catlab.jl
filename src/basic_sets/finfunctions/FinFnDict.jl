module FinFnDict 

export FinFunctionDict

using StructEquality

using GATlab

using ...Sets: AbsSet, SetOb
using ...SetFunctions: AbsFunction, ThSetFunction, SetFunction, dom, codom
using ...FinSets: FinSet

import ..FinFunctions: FinFunction, FinDomFunction

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict{T<:AbsSet}
  val::Dict
  dom::FinSet
  codom::T
  function FinFunctionDict(val::Dict, dom::FinSet, codom::T) where T<:AbsSet
    for e in dom 
      haskey(val, e) || error("Missing key $e ∈ $dom from $val")
    end
    new{T}(val, dom, codom)
  end
end

""" Default assumed domain """
FinFunctionDict(val::Dict, codom::AbsSet) = 
  FinFunctionDict(val, FinSet(Set(collect(keys(val)))), codom)


# Accessor
##########

GATlab.getvalue(f::FinFunctionDict) = f.val

# Other methods
###############

function Base.show(io::IO, f::FinFunctionDict)
  print(io, "Fin")
  f.codom isa FinSet || print(io, "Dom")  
  print(io, "Function($(getvalue(f)), ")
  print(io, f.codom)
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThSetFunction [model::FinFunctionDict{T}] where T begin

  dom()::AbsSet = model.dom

  codom()::T = model.codom

  app(i::Any, )::Any = getvalue(model)[i]

  function postcompose(g::AbsFunction)::AbsFunction 
    C = codom(g)
    (C isa FinSet ? FinFunction : FinDomFunction)(SetFunction(
      FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), C)))
  end
end
  
""" Default `FinFunction` from a `AbstractDict`"""
FinFunction(f::AbstractDict) = FinFunction(f, FinSet(Set(values(f))))

""" Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, cod::FinSet) = 
  FinFunction(SetFunction(FinFunctionDict(f, cod)))

  """ Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, dom::FinSet, cod::FinSet) = 
  FinFunction(SetFunction(FinFunctionDict(f, dom, cod)))


FinDomFunction(f::AbstractDict, cod::AbsSet) = 
  FinDomFunction(SetFunction(FinFunctionDict(f, cod)))

FinDomFunction(f::AbstractDict, dom::FinSet, cod::AbsSet) = 
  FinDomFunction(SetFunction(FinFunctionDict(f, dom, cod)))

end # module
