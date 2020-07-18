"""Fancy Display methods for IJulia
"""
module Display
export vis

import ..Graphviz

using ...CategoricalAlgebra.Graphs

function vis(g::AbstractGraph)
  Graphviz.to_graphviz(PropertyGraph{String}(g))
end

function vis(g::AbstractSymmetricGraph)
  Graphviz.to_graphviz(SymmetricPropertyGraph{String}(g))
end

end
