""" Algorithms on graphs based on C-sets.
"""
module GraphAlgorithms
export connected_components, connected_component_projection, topological_sort

using Compat: isnothing
using DataStructures: Stack
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

# Implemented elsewhere, where coequalizers are available.
function connected_component_projection end

# Traversal
###########

abstract type TopologicalSortAlgorithm end
struct TopologicalSortByDFS <: TopologicalSortAlgorithm end

""" Topological sort of a directed acyclic graph.

The [depth-first search](https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search)
algorithm is adapted from the function
[`topological_sort_by_dfs`](https://github.com/JuliaGraphs/LightGraphs.jl/blob/1c6cf65cc0981250e430bbef39055da23bd25bd0/src/traversals/dfs.jl#L44)
in LightGraphs.jl.
"""
function topological_sort(g::AbstractACSet;
                          alg::TopologicalSortAlgorithm=TopologicalSortByDFS())
  topological_sort(g, alg)
end

function topological_sort(g::AbstractACSet, ::TopologicalSortByDFS)
  vs = Int[]
  marking = fill(Unmarked, nv(g))
  for v in reverse(vertices(g))
    marking[v] == Unmarked || continue
    marking[v] = TempMarked
    stack = Stack{Int}()
    push!(stack, v)
    while !isempty(stack)
      u = first(stack)
      u_out = outneighbors(g, u)
      i = findfirst(u_out) do w
        marking[w] != TempMarked || error("Graph is not acyclic: $g")
        marking[w] == Unmarked
      end
      if isnothing(i)
        marking[u] = Marked
        push!(vs, u)
        pop!(stack)
      else
        w = u_out[i]
        marking[w] = TempMarked
        push!(stack, w)
      end
    end
  end
  reverse!(vs)
end

@enum TopologicalSortDFSMarking Unmarked=0 TempMarked=1 Marked=2

end
