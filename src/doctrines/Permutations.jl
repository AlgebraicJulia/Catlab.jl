""" Computer algebra of the symmetric group.

FIXME: This doesn't really belong under `Doctrines`, since this isn't a
doctrine, but I'm thinking the `Doctrines` top-level module should be renamed.
"""
module Permutations
export decompose_permutation_by_bubble_sort!, permutation_to_expr

using ..Doctrines: compose, id, otimes, munit, braid

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
"""
function permutation_to_expr(σ::Vector{Int}, objects::Vector)
  @assert all(σ[i] == i for i in eachindex(σ)) "Conversion of non-identity not implemented"
  id(otimes(objects))
end

end
