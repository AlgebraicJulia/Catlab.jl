module FinFnDict 

export FinFunctionDict

using StructEquality

using GATlab

using ...FinSets: FinSet
using ..FinFunctions: dom, codom, FinFunction′
import ..FinFunctions: FinFunction, ThFinFunction

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict{D,C}
  val::Dict
  dom::FinSet
  codom::FinSet
  function FinFunctionDict(val::Dict, dom::FinSet, codom::FinSet)
    for e in dom 
      haskey(val, e) || error("Missing key $e ∈ $dom from $val")
    end
    new{eltype(dom),eltype(codom)}(val, dom, codom)
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

@instance ThFinFunction{D,C} [model::FinFunctionDict{D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::FinSet = model.codom

  app(i::D)::C = getvalue(model)[i]
  
  function postcompose(g::FinFunction′)::FinFunction 
    FinFunction(
      FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), codom(g)))
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


end # module
