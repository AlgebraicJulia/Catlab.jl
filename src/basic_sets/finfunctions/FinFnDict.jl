module FinFnDict 

export FinFunctionDict

using StructEquality

using GATlab

using ...Sets: AbsSet, SetOb
using ...SetFunctions: AbsFunction, ThSetFunction, SetFunction, dom, codom
using ...FinSets: FinSet
using ..FinFunctions: specialize
import ..FinFunctions: FinFunction, FinDomFunction

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict
  val::Dict
  dom::FinSet
  codom::AbsSet
  function FinFunctionDict(val::Dict, dom::FinSet, codom::AbsSet)
    for e in dom 
      haskey(val, e) || error("Missing key $e ∈ $dom from $val")
    end
    new(val, dom, codom)
  end
end

""" Default assumed domain """
FinFunctionDict(val::Dict, codom::AbsSet) = 
  FinFunctionDict(val, FinSet(Set(collect(keys(val)))), codom)


GATlab.getvalue(f::FinFunctionDict) = f.val

function Base.show(io::IO, f::FinFunctionDict)
  print(io, "Fin")
  f.codom isa FinSet || print(io, "Dom")  
  print(io, "Function($(getvalue(f)), ")
  print(io, f.codom)
  print(io, ")")
end

# SetFunction implementation
############################

@instance ThSetFunction [model::FinFunctionDict] begin

  dom()::AbsSet = model.dom

  codom()::AbsSet = model.codom

  app(i::Any, )::Any = getvalue(model)[i]

  function postcompose(g::AbsFunction)::AbsFunction 
    C = codom(g)
    specialize(SetFunction(
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
