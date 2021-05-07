module DPOTest
using Test
using Catlab.CategoricalAlgebra.DPO
using Catlab.Graphs.BasicGraphs
using Catlab.CategoricalAlgebra.CSets

# Example graphs
I1 = Graph(1)
I2 = Graph(2)
I3 = Graph(3)

# 1 <- 2 -> 3
span = Graph(3)
add_edges!(span, [2,2],[1,3])
# 1 -> 2
arr = Graph(2)
add_edges!(arr, [1],[2])
# 1 <-> 2
biarr = Graph(2)
add_edges!(biarr, [1,2],[2,1])
# 1 -> 2 -> 3 -> 1 ...
tri = Graph(3)
add_edges!(tri,[1,2,3],[2,3,1])
# 4 <- 1 -> 2 <- 3 -> 4 <- 1 ...
dispan = Graph(4)
add_edges!(dispan, [1,1,3,3],[2,4,2,4])

# 1 -> 2
# |  / ^
# vv   |
# 4 -> 3
squarediag = Graph(4)
add_edges!(squarediag, [1,1,2,3,4],[2,4,4,2,3])

# test match finding
@test match_pat(span,arr).func in [[2,1],[2,3]]
@test match_pat(tri,span) === nothing
@test match_pat(span, tri) === nothing
@test match_pat(dispan, span).func in [[4,1,2],[2,1,4],[4,3,2],[2,3,4]]
@test match_pat(squarediag, tri).func in [[2,4,3],[3,2,4],[4,3,2]]



# REWRITE TESTS
# Add a reverse arrow to span
L = CSetTransformation(I2, arr, V=[1,2])
R = CSetTransformation(I2, biarr, V=[1,2])
m = CSetTransformation(arr, span, V=[2,1], E=[1])
span_w_arrow = Graph(3)
add_edges!(span_w_arrow,[1,1,2],[2,3,1])

@test !(isomorphism(span_w_arrow, rewrite(L, R, m)) === nothing)

# Remove apex of a subspan (top left corner of squarediag, leaves the triangle behind)
L = CSetTransformation(I2, span, V=[1,3])
R = CSetTransformation(I2, I2, V=[1,2])  # identity
m = CSetTransformation(span, squarediag, V=[2,1,4], E=[1,2])
@test !(isomorphism(tri, rewrite(L,R,m)) === nothing)

end
