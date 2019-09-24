""" Computer algebra of the symmetric group.

FIXME: This doesn't really belong under `Doctrines`, since this isn't a
doctrine, but I'm thinking the `Doctrines` top-level module should be renamed.
"""
module Permutations
export decompose_permutation_by_bubble_sort!,
  decompose_permutation_by_insertion_sort!, permutation_to_expr

using Compat
using ...Syntax
using ..Doctrines: dom, codom, compose, id, otimes, munit, braid

# Decomposition
###############

""" Decompose permutation into adjacent transpositions using bubble sort.

An *adjacent transposition*, also known as a *simple transposition*, is a
transposition of form (i i+1), represented here as simply the number i.

This algorithm appears as Algorithm 2.7 in the PhD thesis of Jonathan Huang,
"Probabilistic reasonsing and learning on permutations: Exploiting structural
decompositions of the symmetric group". As Huang notes, the algorithm is
very similar to the well-known bubble sort. It has quadratic complexity.

See also: `decompose_permutation_by_insertion_sort!`
"""
function decompose_permutation_by_bubble_sort!(σ::Vector{Int})::Vector{Int}
  n = length(σ)
  result = Int[]
  for i in 1:n-1
    for j = n-1:-1:i
      if σ[j+1] < σ[j]
        σ[j], σ[j+1] = σ[j+1], σ[j]
        push!(result, j)
      end
    end
  end
  result
end

""" Decompose permutation into adjacent transpositions using insertion sort.

An *adjacent transposition*, also known as a *simple transposition*, is a
transposition of form (i i+1), represented here as simply the number i.

Bubble sort and insertion sort are, in a sense, dual algorithms (Knuth, TAOCP,
Vol 3: Searching and Sort, Sec 5.3.4: Networks for sorting, Figures 45 & 46). A
minimal example on which they give different decompositions is the permutation:

  [1,2,3] ↦ [3,2,1]

See also: `decompose_permutation_by_bubble_sort!`
"""
function decompose_permutation_by_insertion_sort!(σ::Vector{Int})::Vector{Int}
  n = length(σ)
  result = Int[]
  for i in 2:n
    for j in i:-1:2
      if σ[j-1] > σ[j]
        σ[j-1], σ[j] = σ[j], σ[j-1]
        push!(result, j-1)
      end
    end
  end
  result
end

# Conversion to expression
##########################

""" Convert a typed permutation into a morphism expression.

Warning: The morphism expression is not simplified.
"""
function permutation_to_expr(σ::Vector{Int}, xs::Vector; sort::Symbol=:insertion)
  permutation_to_expr!(copy(σ), copy(xs); sort=sort)
end
function permutation_to_expr!(σ::Vector{Int}, xs::Vector; sort::Symbol=:insertion)
  n = length(σ)
  @assert length(xs) == n
  
  transpositions = if sort == :bubble
    decompose_permutation_by_bubble_sort!(σ)
  elseif sort == :insertion
    decompose_permutation_by_insertion_sort!(σ)
  else
    error("Sorting algorithm not supported: $sort")
  end
  if isempty(transpositions)
    return id(otimes(xs))
  end
  
  layers = map(transpositions) do τ
    layer = [
      τ > 1 ? id(otimes(xs[1:τ-1])) : nothing,
      braid(xs[τ], xs[τ+1]),
      τ+1 < n ? id(otimes(xs[τ+2:n])) : nothing,
    ]
    xs[τ], xs[τ+1] = xs[τ+1], xs[τ]
    foldl(otimes, filter(!isnothing, layer))
  end
  foldl(compose, layers)
end

end
