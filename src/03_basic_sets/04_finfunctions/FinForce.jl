module FinForce 

using GATlab: getvalue

using ...FinSets: FinSetInt, FinSet
using ...SetFunctions: SetFunction, dom, codom
import ...SetFunctions: force

using ..FinFunctions: FinDomFunction
using ..FinFnVector: AbsFinFunctionVector
using ..FinFnDict: FinFunctionDict

""" 
Special `force` method for FinDomFunction - we know we can normalize to a 
FinFunctionDict or FinFunctionVect
"""
function force(s::SetFunction{Any,SetFunction,FinSet,D})::SetFunction{Any,SetFunction,FinSet,D} where D
  i = getvalue(s)
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return SetFunction{Any,SetFunction,FinSet,D}(collect(s), codom(s))
  else
    i isa FinFunctionDict && return s 
    return SetFunction{Any,SetFunction,FinSet,D}(
      Dict(k => s(k) for k in dom(s)), codom(s))
  end
end

end # module
