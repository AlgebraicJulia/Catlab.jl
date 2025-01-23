module FinForce 

using ....Theories: dom, codom
using ..FinFunctions
import ..SetFunctions: force

force(f::FinDomFunction) =
  FinDomFunctionDict(Dict(x => f(x) for x in dom(f)), codom(f))

force(f::FinDomFunctionDict) = f

force(f::IndexedFinDomFunctionVector) = f

force(f::FinDomFunction{Int}) = FinDomFunctionVector(map(f, dom(f)), codom(f))

force(f::FinDomFunctionVector) = f

end # module