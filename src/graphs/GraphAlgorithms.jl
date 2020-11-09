""" Algorithms on graphs based on C-sets.
"""
module GraphAlgorithms
export connected_components

import LightGraphs: connected_components

using ...Theories: dom, codom
using ...CSetDataStructures, ..BasicGraphs

# Connectivity
##############

function connected_components(g::AbstractACSet)::Vector{Vector{Int}}
  π = connected_component_projection(g)
  components = [ Int[] for c in codom(π) ]
  for v in dom(π)
    push!(components[π(v)], v)
  end
  components
end

# Implemented later, once coequalizers are available.
function connected_component_projection end

end
