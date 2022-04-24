# Authors: Kris Brown, Tyler Hanks
# Original Repo: https://github.com/kris-brown/Computational-Category-Theoretic-Rewriting/blob/main/src/SSets.jl
using Catlab.Graphs
using Catlab.CategoricalAlgebra
using Catlab.Present
import Catlab.CategoricalAlgebra: elements

# Define C-set
@present ThSemisimplicialSet(FreeSchema) begin
  (V, E, T)::Ob
  (d1, d2, d3)::Hom(T, E)
  (src, tgt)::Hom(E, V)
end
@acset_type SSet(ThSemisimplicialSet)

# Define pattern
"""
V1--e1-→V2
| t1  / |
e2  /   e4
↓ ↙  t2 ↓
V3--e3-→V4
"""
quad = @acset SSet begin
  T = 2
  E = 5
  V = 4
  d1 = [1, 5]
  d2 = [5, 3]
  d3 = [2, 4]
  src = [1, 1, 3, 2, 2]
  tgt = [2, 3, 4, 4, 3]
end

# Define mesh
"""
Box order
...
n n+1 n+2 ...
1  2   3 ...

Edge order


(i+1,j)  ------>(i+1,j+1)
  |         /     |
  v       /       v
(i,j)----------> (i, j+1)
"""
function repeat(n::Int)
  res = @acset SSet begin
    E = (n * (n - 1)) * 2 + (n - 1)^2
    V = n^2
  end
  coord = collect(Iterators.product(1:n, 1:n))
  v_d = Dict([(x, y) => i for (i, (x, y)) in enumerate(coord)])

  h_edge_d = Dict([(x, y) => i for (i, (x, y)) in enumerate(filter(c -> c[2] < n, coord))])

  v_edge_d = Dict([(x, y) => n * (n - 1) + i for (i, (x, y))
                   in
                   enumerate(filter(c -> c[1] < n, coord))])
  d_edge_d = Dict([(x, y) => 2 * n * (n - 1) + i for (i, (x, y))
                   in
                   enumerate(filter(c -> c[1] < n && c[2] < n, coord))])
  for (i, j) in coord
    if haskey(h_edge_d, (i, j))
      set_subparts!(res, h_edge_d[(i, j)]; (src=v_d[(i, j)], tgt=v_d[(i, j + 1)])...)
    end
    if haskey(v_edge_d, (i, j))
      set_subparts!(res, v_edge_d[(i, j)]; (src=v_d[(i + 1, j)], tgt=v_d[(i, j)])...)
    end
    if haskey(d_edge_d, (i, j))
      set_subparts!(res, d_edge_d[(i, j)]; (src=v_d[(i + 1, j + 1)], tgt=v_d[(i, j)])...)
    end
  end
  for (i, j) in filter(c -> c[1] < n && c[2] < n, coord)
    add_part!(res, :T, d1=h_edge_d[(i + 1, j)], d2=d_edge_d[(i, j)], d3=v_edge_d[(i, j)])
    add_part!(res, :T, d1=d_edge_d[(i, j)], d2=h_edge_d[(i, j)], d3=v_edge_d[(i, j + 1)])
  end

  return res

end

function repeat1d(n::Int)
  res = @acset SSet begin
    V = 2 * n
  end

  # Create horizontal edges
  edge_dict = Dict{Tuple{Int,Int},Int}()
  for i in 1:(n-1)
    edge_dict[(i, i + 1)] = add_part!(res, :E, src=i, tgt=i + 1)
    edge_dict[(i + n, i + n + 1)] = add_part!(res, :E, src=i + n, tgt=i + n + 1)
  end
  # Create vertical edges
  for i in 1:n
    edge_dict[(i, i + n)] = add_part!(res, :E, src=i, tgt=i + n)
  end
  # Create diagonal edges
  for i in 2:n
    edge_dict[(i, i + n - 1)] = add_part!(res, :E, src=i, tgt=i + n - 1)
  end

  # Add triangles
  for i in 1:n-1
    add_part!(res, :T, d1=edge_dict[(i, i + 1)], d2=edge_dict[(i + 1, i + n)], d3=edge_dict[(i, i + n)])
    add_part!(res, :T, d1=edge_dict[(i + 1, i + n)], d2=edge_dict[(i + n, i + n + 1)], d3=edge_dict[(i + 1, i + n + 1)])
  end

  return res
end


# Define replacement

"""
d1,d2,d3: d1;d2 = d3

V1--e1-→V2
| \\  t2 |
e2  \\   e4
↓ t1  ↘ ↓
V3--e3-→V4
"""
quad_repl = @acset SSet begin
  T = 2
  E = 5
  V = 4
  d1 = [2, 1]
  d2 = [3, 4]
  d3 = [5, 5]
  src = [1, 1, 3, 2, 1]
  tgt = [2, 3, 4, 4, 4]
end

# Interface
quad_int = @acset SSet begin
  E = 4
  V = 4
  src = [1, 1, 3, 2]
  tgt = [2, 3, 4, 4]
end

function elements(f::ACSetTransformation{S}) where {S}
  X, Y = elements.([dom(f), codom(f)])
  offY = Dict([o => let z = findfirst(==(i), Y[:πₑ])
    isnothing(z) ? 0 : z - 1
  end
               for (i, o) in enumerate(ob(S))])
  pts = vcat([collect(f[o]) .+ offY[o] for o in ob(S)]...)
  hs = homomorphisms(X, Y; initial=Dict([:El => pts]))
  return only(hs)
end


