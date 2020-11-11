""" Categories of graphs and other categorical and algebraic aspects of graphs.
"""
module GraphCategories

using ..FinSets, ..CSets, ..Limits
using ...Graphs.BasicGraphs
import ...Graphs.GraphAlgorithms: connected_component_projection

function connected_component_projection(g::AbstractACSet)::FinFunction{Int}
  proj(coequalizer(FinFunction(src(g), nv(g)),
                   FinFunction(tgt(g), nv(g))))
end

end
