module FinForce 

using GATlab: getvalue

using ...FinSets: FinSetInt, FinSet, AbsSet
using ...SetFunctions: SetFunction, dom, codom
import ...SetFunctions: force

using ..FinFunctions, ..FinFnVector, ..FinFnDict

""" 
Special `force` method for FinDomFunction - we know we can normalize to a 
FinFunctionDict or FinFunctionVect
"""
function force(s::Fin_FinDom)
  i = getvalue(s)
  F = s isa FinFunction ? FinFunction : FinDomFunction
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return F([s(elem) for elem in dom(s)], dom(s), codom(s); index=is_indexed(s))
  else
    i isa FinFunctionDict && return s 
    return F(Dict(k => s(k) for k in dom(s)), dom(s), codom(s))
  end
end

end # module
