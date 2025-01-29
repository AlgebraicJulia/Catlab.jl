"""
`force` behaves differently when the domain is finite because we can compute 
a normal form. This should really be called "normalize". It coerces the 
function to a `FinFnVector` (if dom is `FinSetInt`) or `FinFnDict` (otherwise).
"""
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
function force(s::AbsFinDomFunction)
  i = getvalue(getvalue(s))
  F = s isa FinFunction ? FinFunction : FinDomFunction
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return F([s(elem) for elem in dom(s)], dom(s), codom(s); index=is_indexed(i))
  else
    i isa FinFunctionDict && return s 
    return F(Dict(k => s(k) for k in dom(s)), dom(s), codom(s))
  end
end

end # module
