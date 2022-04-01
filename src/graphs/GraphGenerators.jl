module GraphGenerators
export path_graph, cycle_graph, complete_graph, star_graph, wheel_graph,
  parallel_arrows, erdos_renyi, expected_degree_graph, watts_strogatz

using ...CSetDataStructures, ..BasicGraphs
using ...CSetDataStructures: hom
using Random
using Random: GLOBAL_RNG

""" Path graph on ``n`` vertices.
"""
function path_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:(n-1), 2:n; E...)
  g
end

""" Cycle graph on ``n`` vertices.

When ``n = 1``, this is a loop graph.
"""
function cycle_graph(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  add_edges!(g, 1:n, circshift(1:n, -1); E...)
  g
end

""" Complete graph on ``n`` vertices.
"""
function complete_graph(::Type{T}, n::Int; V=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n; V...)
  for i in vertices(g), j in vertices(g)
    if i != j && (is_directed(T) || i < j)
      add_edge!(g, i, j)
    end
  end
  g
end

""" Star graph on ``n`` vertices.

In the directed case, the edges point outward.
"""
function star_graph(::Type{T}, n::Int; E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, n)
  add_edges!(g, fill(n,n-1), 1:(n-1); E...)
  g
end

""" Wheel graph on ``n`` vertices.

In the directed case, the outer cycle is directed and the spokes point outward.
"""
function wheel_graph(::Type{T}, n::Int) where T <: ACSet
  g = cycle_graph(T, n-1)
  add_vertex!(g)
  add_edges!(g, fill(n,n-1), 1:(n-1))
  g
end

""" Graph with two vertices and ``n`` parallel edges.
"""
function parallel_arrows(::Type{T}, n::Int; V=(;), E=(;)) where T <: ACSet
  g = T()
  add_vertices!(g, 2; V...)
  add_edges!(g, fill(1,n), fill(2,n); E...)
  g
end

# Should this be exported from `BasicGraphs`?
@generated is_directed(::Type{T}) where {S, T<:StructACSet{S}} = :inv ∉ hom(S)

getRNG(seed::Integer, rng::AbstractRNG) = seed >= 0 ? MersenneTwister(seed) : rng

"""
    randbn(n, p, seed=-1)

Return a binomally-distribted random number with parameters `n` and `p` and optional `seed`.

### Optional Arguments
- `seed=-1`: set the RNG seed.
- `rng`: set the RNG directly

### References
- "Non-Uniform Random Variate Generation," Luc Devroye, p. 522. Retrieved via http://www.eirene.de/Devroye.pdf.
- http://stackoverflow.com/questions/23561551/a-efficient-binomial-random-number-generator-code-in-java
- https://github.com/JuliaGraphs/LightGraphs.jl/blob/2a644c2b15b444e7f32f73021ec276aa9fc8ba30/src/SimpleGraphs/generators/randgraphs.jl#L90
"""
function randbn(n::Integer, p::Real; rng::AbstractRNG=GLOBAL_RNG)
  log_q = log(1.0 - p)
  x = 0
  sum = 0.0
  while true
    sum += log(rand(rng)) / (n - x)
    sum < log_q && break
    x += 1
  end
  return x
end

"""
    erdos_renyi(GraphType, n, p)

Create an [Erdős–Rényi](http://en.wikipedia.org/wiki/Erdős–Rényi_model)
random graph with `n` vertices. Edges are added between pairs of vertices with
probability `p`.

### Optional Arguments
- `seed=-1`: set the RNG seed.
- `rng`: set the RNG directly

### References
- https://github.com/JuliaGraphs/LightGraphs.jl/blob/2a644c2b15b444e7f32f73021ec276aa9fc8ba30/src/SimpleGraphs/generators/randgraphs.jl
"""
function erdos_renyi(::Type{T}, n::Int, p::Real; V=(;),
                     seed::Int=-1, rng::AbstractRNG=GLOBAL_RNG) where T <: ACSet
  rng = getRNG(seed,rng)
  _erdos_renyi(T,n,p,V,rng)
end

function _erdos_renyi(::Type{T}, n::Int, p::Real, V, rng::AbstractRNG) where T <: ACSet
  p >= 1 && return complete_graph(T, n)
  maxe = n * (n-1)
  m = randbn(maxe,p;rng=rng)
  return _erdos_renyi(T,n,m,V,rng)
end


"""
    erdos_renyi(GraphType, n, ne)

Create an [Erdős–Rényi](http://en.wikipedia.org/wiki/Erdős–Rényi_model) random
graph with `n` vertices and `ne` edges.

### References
- https://github.com/JuliaGraphs/LightGraphs.jl/blob/2a644c2b15b444e7f32f73021ec276aa9fc8ba30/src/SimpleGraphs/generators/randgraphs.jl
"""
function erdos_renyi(::Type{T}, n::Int, m::Int; V=(;),
                     seed::Int=-1, rng::AbstractRNG=GLOBAL_RNG) where T <: ACSet
  rng = getRNG(seed, rng)
  _erdos_renyi(T,n,m,V,rng)
end

function _erdos_renyi(::Type{T}, n::Int, m::Int, V, rng::AbstractRNG) where T <: ACSet
  maxe = n * (n-1)
  maxe == m && return complete_graph(T, n)
  @assert(m <= maxe, "Maximum number of edges for this graph is $maxe")
  # In the case of a symmetric graph, the edges are double-counted
  totale = is_directed(T) ? m : 2*m
  k = Int(ceil(m/n))

  g = T()
  add_vertices_with_indices!(g, n, k)
  set_subparts!(g,:V,V)

  while ne(g) < totale
    src = rand(rng, 1:n)
    tgt = rand(rng, 1:n)
    src != tgt && !has_edge(g,src,tgt) && add_edge!(g,src,tgt)
  end

  return g
end


"""
    expected_degree_graph(GraphType, ω)

Given a vector of expected degrees `ω` indexed by vertex, create a random undirected graph in which vertices `i` and `j` are
connected with probability `ω[i]*ω[j]/sum(ω)`.

### Optional Arguments
- `seed=-1`: set the RNG seed.
- `rng`: set the RNG directly

### Implementation Notes
The algorithm should work well for `maximum(ω) << sum(ω)`. As `maximum(ω)` approaches `sum(ω)`, some deviations
from the expected values are likely.

### References
- Connected Components in Random Graphs with Given Expected Degree Sequences, Linyuan Lu and Fan Chung. [https://link.springer.com/article/10.1007%2FPL00012580](https://link.springer.com/article/10.1007%2FPL00012580)
- Efficient Generation of Networks with Given Expected Degrees, Joel C. Miller and Aric Hagberg. [https://doi.org/10.1007/978-3-642-21286-4_10](https://doi.org/10.1007/978-3-642-21286-4_10)
- https://github.com/JuliaGraphs/LightGraphs.jl/blob/2a644c2b15b444e7f32f73021ec276aa9fc8ba30/src/SimpleGraphs/generators/randgraphs.jl#L187
"""
function expected_degree_graph(::Type{T},ω::Vector{<:Real}; V=(;),
                               seed::Int=-1, rng::AbstractRNG=GLOBAL_RNG) where T <: ACSet
  rng = getRNG(seed, rng)
  g = T()
  add_vertices!(g,length(ω);V...)
  expected_degree_graph!(g, ω, rng=rng)
end

function expected_degree_graph!(g::T, ω::Vector{U};
                                seed::Int=-1, rng::AbstractRNG=GLOBAL_RNG) where {T <: ACSet, U <: Real}
  rng = getRNG(seed, rng)
  n = length(ω)
  @assert all(zero(U) .<= ω .<= n - one(U)) "Elements of ω need to be at least 0 and at most n-1"

  π = sortperm(ω, rev=true)

  S = sum(ω)

  for u = 1:(n - 1)
    v = u + 1
    p = min(ω[π[u]] * ω[π[v]] / S, one(U))
    while v <= n && p > zero(p)
      if p != one(U)
        v += floor(Int, log(rand(rng)) / log(one(U) - p))
      end
      if v <= n
        q = min(ω[π[u]] * ω[π[v]] / S, one(U))
        if rand(rng) < q / p
          add_edge!(g, π[u], π[v])
        end
        p = q
        v += 1
      end
    end
  end
  return g
end

"""
    watts_strogatz(n, k, β)

Return a [Watts-Strogatz](https://en.wikipedia.org/wiki/Watts_and_Strogatz_model)
small world random graph with `n` vertices, each with expected degree `k` (or `k
- 1` if `k` is odd). Edges are randomized per the model based on probability `β`.

The algorithm proceeds as follows. First, a perfect 1-lattice is constructed,
where each vertex has exacly `div(k, 2)` neighbors on each side (i.e., `k` or
`k - 1` in total). Then the following steps are repeated for a hop length `i` of
`1` through `div(k, 2)`.

1. Consider each vertex `s` in turn, along with the edge to its `i`th nearest
   neighbor `t`, in a clockwise sense.

2. Generate a uniformly random number `r`. If `r ≥ β`, then the edge `(s, t)` is
   left unaltered. Otherwise, the edge is deleted and *rewired* so that `s` is
   connected to some vertex `d`, chosen uniformly at random from the entire
   graph, excluding `s` and its neighbors. (Note that `t` is a valid candidate.)

For `β = 0`, the graph will remain a 1-lattice, and for `β = 1`, all edges will
be rewired randomly.

### Optional Arguments
- `is_directed=false`: if true, return a directed graph.
- `seed=-1`: set the RNG seed.

### References
- Collective dynamics of ‘small-world’ networks, Duncan J. Watts, Steven H. Strogatz. [https://doi.org/10.1038/30918](https://doi.org/10.1038/30918)
- Small Worlds, Duncan J. watts. [https://en.wikipedia.org/wiki/Special:BookSources?isbn=978-0691005416](https://en.wikipedia.org/wiki/Special:BookSources?isbn=978-0691005416)
- https://github.com/JuliaGraphs/LightGraphs.jl/blob/2a644c2b15b444e7f32f73021ec276aa9fc8ba30/src/SimpleGraphs/generators/randgraphs.jl#L187
"""
function watts_strogatz(::Type{T}, n::Integer, k::Integer, β::Real;
                        seed::Int=-1, rng::AbstractRNG=GLOBAL_RNG) where T <: ACSet
  rng = getRNG(seed, rng)
  _watts_strogatz(T,n,k,β,rng)
end

function _watts_strogatz(::Type{T}, n::Integer, k::Integer, β::Real,
                         rng::AbstractRNG) where T <: ACSet
  @assert k < n

  # If we have n - 1 neighbors (exactly k/2 on each side), then the graph is
  # necessarily complete. No need to run the Watts-Strogatz procedure:
  if k == n - 1 && iseven(k)
    return complete_graph(T,n)
  end

  g = T()
  add_vertices_with_indices!(g, n, k)

  # The ith next vertex, in clockwise order.
  # (Reduce to zero-based indexing, so the modulo works, by subtracting 1
  # before and adding 1 after.)
  @inline target(s, i) = ((s + i - 1) % n) + 1

  # Phase 1: For each step size i, add an edge from each vertex s to the ith
  # next vertex, in clockwise order.

  for i = 1:div(k, 2), s = 1:n
    add_edge!(g, s, target(s, i))
  end

  # Phase 2: For each step size i and each vertex s, consider the edge to the
  # ith next vertex, in clockwise order. With probability β, delete the edge
  # and rewire it to any (valid) target, chosen uniformly at random.

  for i = 1:div(k, 2), s = 1:n

    # We only rewire with a probability β, and we only worry about rewiring
    # if there is some vertex not connected to s; otherwise, the only valid
    # rewiring is to reconnect to the ith next vertex, and there is no work
    # to do.
    (rand(rng) < β && degree(g, s) < n - 1) || continue

    t = target(s, i)

    while true
      d = rand(1:n)               # Tentative new target
      d == s && continue          # Self-loops prohibited
      d == t && break             # Rewired to original target
      if !(has_edge(g,s,d))       # Was this valid (i.e., unconnected)?
        add_edge!(g, s, d)        # True rewiring: Add new edge
        rem_edge!(g, s, t)        # True rewiring: Delete original edge
        break                     # We found a valid target
      end
    end

  end
  return g
end

end
