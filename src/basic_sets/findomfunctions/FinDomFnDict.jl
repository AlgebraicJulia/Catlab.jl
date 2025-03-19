module FinDomFnDict 

export FinDomFunctionDict

using StructEquality

using GATlab

using ...BasicSets
import ..FinDomFunctions: FinFunction, FinDomFunction, ThFinDomFunction, FinDomFunction′

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict{D,C}
  val::Dict
  dom::FinSet
  codom::SetOb
  function FinFunctionDict(val::Dict, dom::FinSet, codom::SetOb)
    for e in dom 
      haskey(val, e) || error("Missing key $e ∈ $dom from $val")
    end
    new{eltype(dom),eltype(codom)}(val, dom, codom)
  end
end

""" Default assumed domain """
FinFunctionDict(val::Dict, codom::SetOb) = 
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

@instance ThFinDomFunction{D,C} [model::FinFunctionDict{D,C}] where {D,C} begin

  dom()::FinSet = model.dom

  codom()::SetOb = model.codom

  app(i::D)::C = getvalue(model)[i]

  # precompose(f::FinFunction) = precompose(model, f)
  
  function postcompose(g::SetFunction)::FinDomFunction 
    FinDomFunction(
      FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), codom(g)))
  end
end
  
FinDomFunction(f::AbstractDict, cod::SetOb) = 
  FinDomFunction(FinFunctionDict(f, cod))

FinDomFunction(f::AbstractDict, dom::FinSet, cod::SetOb) = 
  FinDomFunction(FinFunctionDict(f, dom, cod))

end # module
