""" Computer algebra of the symmetric group.

FIXME: This doesn't really belong under `Doctrines`, since this isn't a
doctrine, but I'm thinking the `Doctrines` top-level module should be renamed.
"""
module Permutations
export decompose_permutation_by_bubble_sort!, permutation_to_expr

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
"""
function decompose_permutation_by_bubble_sort!(σ::Vector{Int})::Vector{Int}
  n = length(σ)
  result = Int[]
  for i in 1:n
    for j = n-1:-1:i
      if σ[j+1] < σ[j]
        σ[j], σ[j+1] = σ[j+1], σ[j]
        push!(result, j)
      end
    end
  end
  result
end

# Conversion to expression
##########################

""" Convert a typed permutation into a morphism expression.

FIXME: The resulting expression is not simplified.
"""
function permutation_to_expr(σ::Vector{Int}, xs::Vector)
  permutation_to_expr!(copy(σ), copy(xs))
end
function permutation_to_expr!(σ::Vector{Int}, xs::Vector)
  n = length(σ)
  @assert length(xs) == n
  
  transpositions = decompose_permutation_by_bubble_sort!(σ)
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
