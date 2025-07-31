module TestPermutations

using Test
using Catlab.Theories, Catlab.CategoricalAlgebra.Misc.Permutations

# Decomposition
###############

const bubble_sort = adjacent_transpositions_by_bubble_sort!
const insertion_sort = adjacent_transpositions_by_insertion_sort!

# Permutations in Sym(1)
@test cycles([1]) == [[1]]
@test bubble_sort([1]) == []
@test insertion_sort([1]) == []

# Permutations in Sym(2)
@test cycles([1,2]) == [[1],[2]]
@test cycles([2,1]) == [[1,2]]
@test bubble_sort([1,2]) == []
@test bubble_sort([2,1]) == [1]
@test insertion_sort([1,2]) == []
@test insertion_sort([2,1]) == [1]

# Permutations in Sym(3)
@test cycles([1,2,3]) == [[1],[2],[3]]
@test cycles([2,1,3]) == [[1,2],[3]]
@test cycles([1,3,2]) == [[1],[2,3]]
@test cycles([2,3,1]) == [[1,2,3]]
@test cycles([3,1,2]) == [[1,3,2]]
@test cycles([3,2,1]) == [[1,3],[2]]
@test bubble_sort([1,2,3]) == []
@test bubble_sort([2,1,3]) == [1]
@test bubble_sort([1,3,2]) == [2]
@test bubble_sort([2,3,1]) == [2,1]
@test bubble_sort([3,1,2]) == [1,2]
@test bubble_sort([3,2,1]) == [2,1,2]
@test insertion_sort([1,2,3]) == []
@test insertion_sort([2,1,3]) == [1]
@test insertion_sort([1,3,2]) == [2]
@test insertion_sort([2,3,1]) == [2,1]
@test insertion_sort([3,1,2]) == [1,2]
@test insertion_sort([3,2,1]) == [1,2,1]

# Converson to expression
#########################

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)

# Permutations in Sym(1)
@test permutation_to_expr([1], [A]) == id(A)

# Permutations in Sym(2)
@test permutation_to_expr([1,2], [A,B]) == id(otimes(A,B))
@test permutation_to_expr([2,1], [A,B]) == braid(A,B)

# Permutations in Sym(3)
@test permutation_to_expr([1,2,3], [A,B,C]) == id(otimes(A,B,C))
@test permutation_to_expr([2,1,3], [A,B,C]) == otimes(braid(A,B),id(C))
@test permutation_to_expr([1,3,2], [A,B,C]) == otimes(id(A), braid(B,C))
@test permutation_to_expr([2,3,1], [A,B,C]) ==
  compose(otimes(id(A),braid(B,C)), otimes(braid(A,C),id(B)))
@test permutation_to_expr([3,1,2], [A,B,C]) ==
  compose(otimes(braid(A,B),id(C)), otimes(id(B),braid(A,C)))

end
