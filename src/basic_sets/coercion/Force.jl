# Should we have two different notions of forcing?
# One which performs simplification (e.g. collapsing two composed vectors into one vector)
# One which performs normalization (id(3) is simpler than [1,2,3], but the latter is a better normal form)
module Force 

using GATlab: getvalue

using ..BasicSets: FinSetInt, SetFunction, dom, codom, postcompose, 
  ConstantFunction, CompositeFunction, FinFunction, AbsFinFunctionVector,
  FinFunctionDict, is_indexed
import ..BasicSets: force

"""
Simplification of `SetFunction`. This is where `postcompose` gets used to 
reduce composites into non-composites.  
"""
function force(s::SetFunction)::SetFunction
  i = getvalue(s)
  i isa CompositeFunction || return s 

  # Recursively simplify the components
  f, g = force.(SetFunction.(getvalue.([first(i), last(i)])))
  
  # Optimization: we want to precompose w/ `f` rather than postcompose w/ `g`
  getvalue(g) isa ConstantFunction && return SetFunction(
    ConstantFunction(getvalue(getvalue(g)), dom(f), codom(g)))
  
  return postcompose(f, g)
end

force(::Nothing) = nothing

""" 
Special `force` method for FinDomFunction - we know we can normalize to a 
FinFunctionDict or FinFunctionVect
"""
function force(s::FinFunction)::FinFunction
  i = getvalue(s)
  if getvalue(dom(s)) isa FinSetInt
    i isa AbsFinFunctionVector && return s
    return FinFunction([s(elem) for elem in dom(s)], dom(s), codom(s); index=is_indexed(s))
  else
    i isa FinFunctionDict && return s 
    return FinFunction(Dict(k => s(k) for k in dom(s)), dom(s), codom(s))
  end
end

end # module
