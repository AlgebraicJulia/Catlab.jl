module TestPermutations

using Test
using Catlab.Doctrines, Catlab.Doctrines.Permutations

# Decomposition
###############

const bubble = decompose_permutation_by_bubble_sort!

# Permutations in S(1)
@test bubble([1]) == []

# Permutations in S(2)
@test bubble([1,2]) == []
@test bubble([2,1]) == [1]

# Permutations in S(3)
@test bubble([1,2,3]) == []
@test bubble([2,1,3]) == [1]
@test bubble([1,3,2]) == [2]
@test bubble([2,3,1]) == [2,1]
@test bubble([3,1,2]) == [1,2]
@test bubble([3,2,1]) == [2,1,2]

# Converson to expression
#########################

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)

@test permutation_to_expr([1,2,3], [A,A,A]) == id(otimes(A,A,A))

end
