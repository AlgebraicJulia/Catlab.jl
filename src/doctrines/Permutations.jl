""" Computer algebra of the symmetric group.

FIXME: This doesn't really belong under `Doctrines`, since this isn't a
doctrine, but I'm thinking the `Doctrines` top-level module should be renamed.
"""
module Permutations
export permutation_to_expr

using ..Doctrines: compose, id, otimes, munit, braid


""" Convert a typed permutation into a morphism expression.
"""
function permutation_to_expr(σ::Vector{Int}, objects::Vector)
  @assert all(σ[i] == i for i in eachindex(σ)) "Conversion of non-identity not implemented"
  id(otimes(objects))
end

end
