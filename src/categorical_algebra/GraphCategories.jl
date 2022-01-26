""" Categories of graphs and other categorical and algebraic aspects of graphs.
"""
module GraphCategories

using DataStructures

using ..FinSets, ...ACSetInterface, ..Limits
using ...Graphs.BasicGraphs
import ...Graphs.GraphAlgorithms: connected_component_projection,
  connected_component_projection_bfs

function connected_component_projection(g::ACSet)::FinFunction
  proj(coequalizer(FinFunction(src(g), nv(g)),
                   FinFunction(tgt(g), nv(g))))
end

# This algorithm is linear in the number of vertices of g, so it should be
# significantly faster than the previous one in some cases.
function connected_component_projection_bfs(g::ACSet)
  label = zeros(Int, nv(g))

  q = Queue{Int}()
  for v in 1:nv(g)
    label[v] != 0 && continue
    label[v] = v
    empty!(q)
    enqueue!(q, v)
    while !isempty(q)
      src = dequeue!(q)
      for vertex in neighbors(g, src)
        if label[vertex] == 0
          enqueue!(q,vertex)
          label[vertex] = v
        end
      end
    end
  end

  normalize_labeling(label)
end

end
