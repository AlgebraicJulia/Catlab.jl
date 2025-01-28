# Should we have two different notions of forcing?
# One which performs simplification (e.g. collapsing two composed vectors into one vector)
# One which performs normalization (id(3) is simpler than [1,2,3], but the latter is a better normal form)
module Force 
export force

using GATlab: getvalue

import ...Sets: force
using ...FinSets: FinSetInt

using ..SetFunctions: SetFunction, dom, codom, postcompose
using ..ConstFn: ConstantFunction
using ..CompFn: CompositeFunction

"""
Simplification of `SetFunction`. This is where `postcompose` gets used to 
reduce composites into non-composites.  
"""
function force(s::SetFunction{Any,SetFunction,C,D})::SetFunction{Any,SetFunction,C,D} where {C,D}
  i = getvalue(s)
  i isa CompositeFunction || return s 

  # Recursively simplify the components
  f, g = force.([first(i), last(i)]) 
  
  # Optimization: we want to precompose w/ `f` rather than postcompose w/ `g`
  getvalue(g) isa ConstantFunction && return SetFunction(
    ConstantFunction(getvalue(getvalue(g)), dom(f), codom(g)))
  
  return postcompose(f, g)
end

force(::Nothing) = nothing

end # module
