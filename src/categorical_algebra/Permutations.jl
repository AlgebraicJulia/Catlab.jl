""" Computing with permutations: the computer algebra of the symmetric group.
"""
module Permutations
export cycles,
  permutation_to_expr,
  adjacent_transpositions_by_bubble_sort!,
  adjacent_transpositions_by_insertion_sort!

using ...Syntax
using ...Theories: dom, codom, compose, id, otimes, munit, braid

# Decomposition
###############

""" Decompose a permutation into its cycles.

Returns a vector of vectors, the cycles of the permutation.
"""
cycles(σ::AbstractVector{Int}) = cycles(i -> σ[i], length(σ))

function cycles(σ, n::Int)
  cycles = Vector{Int}[]
  used = falses(n)
  for i in 1:n
    if used[i]
      continue
    end
    cycle, j = Int[], i
    while true
      push!(cycle, j)
      used[j] = true
      j = σ(j)
      @assert 1 <= j <= n
      if j == i
        break
      end
    end
    push!(cycles, cycle)
  end
  cycles
end

""" Decompose permutation into adjacent transpositions using bubble sort.

An *adjacent transposition*, also known as a *simple transposition*, is a
transposition of form (i i+1), represented here as simply the number i.

This algorithm appears as Algorithm 2.7 in the PhD thesis of Jonathan Huang,
"Probabilistic reasonsing and learning on permutations: Exploiting structural
decompositions of the symmetric group". As Huang notes, the algorithm is
very similar to the well-known bubble sort. It has quadratic complexity.

See also: [`adjacent_transpositions_by_insertion_sort!`](@ref).
"""
function adjacent_transpositions_by_bubble_sort!(σ::AbstractVector{Int})
  n = length(σ)
  transpositions = Int[]
  for i in 1:(n - 1)
    for j in (n - 1):-1:i
      if σ[j + 1] < σ[j]
        σ[j], σ[j + 1] = σ[j + 1], σ[j]
        push!(transpositions, j)
      end
    end
  end
  transpositions
end

""" Decompose permutation into adjacent transpositions using insertion sort.

An *adjacent transposition*, also known as a *simple transposition*, is a
transposition of form (i i+1), represented here as simply the number i.

Bubble sort and insertion sort are, in a sense, dual algorithms (Knuth, TAOCP,
Vol 3: Searching and Sort, Sec 5.3.4: Networks for sorting, Figures 45 & 46). A
minimal example on which they give different decompositions is the permutation:

  [1,2,3] ↦ [3,2,1]

See also: [`adjacent_transpositions_by_bubble_sort!`](@ref).
"""
function adjacent_transpositions_by_insertion_sort!(σ::AbstractVector{Int})
  n = length(σ)
  transpositions = Int[]
  for i in 2:n
    for j in i:-1:2
      if σ[j - 1] > σ[j]
        σ[j - 1], σ[j] = σ[j], σ[j - 1]
        push!(transpositions, j - 1)
      end
    end
  end
  transpositions
end

# Conversion to expression
##########################

""" Convert a typed permutation into a morphism expression.

Warning: The morphism expression is not simplified.
"""
function permutation_to_expr(
  σ::AbstractVector{Int},
  xs::AbstractVector;
  sort::Symbol=:insertion,
)
  permutation_to_expr!(copy(σ), copy(xs); sort=sort)
end
function permutation_to_expr!(
  σ::AbstractVector{Int},
  xs::AbstractVector;
  sort::Symbol=:insertion,
)
  n = length(σ)
  @assert length(xs) == n

  transpositions = if sort == :bubble
    adjacent_transpositions_by_bubble_sort!(σ)
  elseif sort == :insertion
    adjacent_transpositions_by_insertion_sort!(σ)
  else
    error("Sorting algorithm not supported: $sort")
  end
  if isempty(transpositions)
    return id(otimes(xs))
  end

  layers = map(transpositions) do τ
    layer = [
      τ > 1 ? id(otimes(xs[1:(τ - 1)])) : nothing,
      braid(xs[τ], xs[τ + 1]),
      τ + 1 < n ? id(otimes(xs[(τ + 2):n])) : nothing,
    ]
    xs[τ], xs[τ + 1] = xs[τ + 1], xs[τ]
    foldl(otimes, filter(!isnothing, layer))
  end
  foldl(compose, layers)
end

end
