module FinFnDict 

export FinFunctionDict

using StructEquality

using GATlab
import GATlab: getvalue

using ...Sets: AbsSet, SetOb
using ...SetFunctions: SetFunctionImpl, ThSetFunction, SetFunction, dom, codom
using ...FinSets: FinSet
import ..FinFunctions: FinFunction, FinDomFunction

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict <: SetFunctionImpl
  val::Dict
  codom::AbsSet
end

# Accessor
##########

getvalue(f::FinFunctionDict) = f.val

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

@instance ThSetFunction{Any, AbsSet, SetFunction} [model::FinFunctionDict] begin

  dom()::AbsSet = FinSet(Set(collect(keys(getvalue(model)))))

  codom()::AbsSet = model.codom

  app(i::Any, )::Any = getvalue(model)[i]

  postcompose(g::SetFunction)::SetFunction = FinDomFunction(
    FinFunctionDict(Dict(k => g(v) for (k,v) in getvalue(model)), codom(g)))

end
  
""" Default `FinFunction` from a `AbstractDict`"""
FinFunction(f::AbstractDict) = FinFunction(f, FinSet(Set(values(f))))

""" Default `FinFunction` from a `AbstractDict` and codom"""
FinFunction(f::AbstractDict, cod::FinSet) = 
  FinFunction(FinFunctionDict(f, cod))

FinDomFunction(f::AbstractDict, cod::AbsSet) = 
  FinDomFunction(FinFunctionDict(f, cod))

end # module
