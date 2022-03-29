module Searching
export bfs_parents, bfs_tree, dfs_parents, dfs_tree

using ...CSetDataStructures, ..BasicGraphs

"""
    tree(parents)
Convert a parents array into a directed graph.
"""
function tree(parents::AbstractVector{Int})
    n = T(length(parents))
    t = Graph(n)
    for (v, u) in enumerate(parents)
        if u > 0 && u != v
            add_edge!(t, u, v)
        end
    end
    return t
end

"""
    bfs_parents(g, s[; dir=:out])

Perform a breadth-first search of graph `g` starting from vertex `s`.
Return a vector of parent vertices indexed by vertex. If `dir` is specified,
use the corresponding edge direction (`:in` and `:out` are acceptable values).



### Performance
This implementation is designed to perform well on large graphs. There are
implementations which are marginally faster in practice for smaller graphs,
but the performance improvements using this implementation on large graphs
can be significant.
"""
bfs_parents(g::ACSet, s::Int; dir = :out) =
    (dir == :out) ? _bfs_parents(g, s, outneighbors) : _bfs_parents(g, s, inneighbors)

function _bfs_parents(g::ACSet, source, neighborfn::Function)
    n = nv(g)
    visited = falses(n)
    parents = zeros(Int, nv(g))
    cur_level = Int[]
    sizehint!(cur_level, n)
    next_level = Int[]
    sizehint!(next_level, n)
    @inbounds for s in source
        visited[s] = true
        push!(cur_level, s)
        parents[s] = s
    end
    while !isempty(cur_level)
        @inbounds for v in cur_level
            @inbounds @simd for i in neighborfn(g, v)
                if !visited[i]
                    push!(next_level, i)
                    parents[i] = v
                    visited[i] = true
                end
            end
        end
        empty!(cur_level)
        cur_level, next_level = next_level, cur_level
        sort!(cur_level)
    end
    return parents
end

"""
    bfs_tree(g, s[; dir=:out])
Provide a breadth-first traversal of the graph `g` starting with source vertex `s`,
and return a directed acyclic graph of vertices in the order they were discovered.
If `dir` is specified, use the corresponding edge direction (`:in` and `:out` are
acceptable values).
"""
bfs_tree(g::ACSet, s::Integer; dir = :out) = tree(bfs_parents(g, s; dir = dir))

"""
    dfs_parents(g, s[; dir=:out])

Perform a depth-first search of graph `g` starting from vertex `s`.
Return a vector of parent vertices indexed by vertex. If `dir` is specified,
use the corresponding edge direction (`:in` and `:out` are acceptable values).

### Implementation Notes
This version of DFS is iterative.
"""
dfs_parents(g::ACSet, s::Integer; dir=:out) =
    (dir == :out) ? _dfs_parents(g, s, outneighbors) : _dfs_parents(g, s, inneighbors)

function _dfs_parents(g::ACSet, s::Int, neighborfn::Function)
    parents = zeros(Int, nv(g))
    seen = zeros(Bool, nv(g))
    S = [s]
    seen[s] = true
    parents[s] = s
    while !isempty(S)
        v = S[end]
        u = 0
        for n in neighborfn(g, v)
            if !seen[n]
                u = n
                break
            end
        end
        if u == 0
            pop!(S)
        else
            seen[u] = true
            push!(S, u)
            parents[u] = v
        end
    end
    return parents
end

"""
    dfs_tree(g, s)

Return a directed acyclic graph based on
depth-first traversal of the graph `g` starting with source vertex `s`.
"""
dfs_tree(g::AbstractGraph, s::Integer; dir=:out) = tree(dfs_parents(g, s; dir=dir))

end
