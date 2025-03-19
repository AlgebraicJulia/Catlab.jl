"""
`force` behaves differently when the domain is finite because we can compute 
a normal form. This should really be called "normalize". It coerces the 
function to a `FinFnVector` (if dom is `FinSetInt`) or `FinFnDict` (otherwise).
"""
module FinForce 

using GATlab: getvalue

using ...BasicSets
using ..FinDomFunctions
import ...SetFunctions: force

using ..FinFunctions, ..FinFnVector, ..FinFnDict

function force(s::FinDomFunction)::FinDomFunction
  i = getvalue(s)
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return FinDomFunction([s(elem) for elem in dom(s)], dom(s), codom(s); index=is_indexed(i))
  else
    i isa FinFunctionDict && return s 
    return FinDomFunction(Dict(k => s(k) for k in dom(s)), dom(s), codom(s))
  end
end


end # module
