module FinFnDict 
export FinFunctionDict, FinDomFunctionDict

using StructEquality

import ....Theories: dom, codom
using ..Sets, ..FinSets, ..FinFunctions, ..SetFunctions


# Dict-based functions
#---------------------

""" Function in **Set** represented by a dictionary.

The domain is a `FinSet{S}` where `S` is the type of the dictionary's `keys`
collection.
"""
@struct_hash_equal struct FinDomFunctionDict{K,D<:AbstractDict{K},Codom<:SetOb} <:
    SetFunction{FinSetCollection{Base.KeySet{K,D},K},Codom}
  func::D
  codom::Codom
end

FinDomFunctionDict(d::AbstractDict{K,V}) where {K,V} =
  FinDomFunctionDict(d, TypeSet{V}())

dom(f::FinDomFunctionDict) = FinSet(keys(f.func))

(f::FinDomFunctionDict)(x) = f.func[x]

function Base.show(io::IO, f::F) where F <: FinDomFunctionDict
  SetFunctions.show_type_constructor(io, F)
  print(io, "(")
  show(io, f.func)
  print(io, ", ")
  SetFunctions.show_domains(io, f, domain=false)
  print(io, ")")
end


""" Function in **FinSet** represented by a dictionary.
"""
const FinFunctionDict{K,D<:AbstractDict{K},Codom<:FinSet} =
  FinDomFunctionDict{K,D,Codom}

FinFunctionDict(d::AbstractDict, codom::FinSet) = FinDomFunctionDict(d, codom)
FinFunctionDict(d::AbstractDict{K,V}) where {K,V} =
  FinDomFunctionDict(d, FinSet(Set(values(d))))

end # module
