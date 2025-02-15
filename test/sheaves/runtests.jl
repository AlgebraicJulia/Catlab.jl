module TestSheaves 

using Test, Catlab
using Catlab.CategoricalAlgebra.Misc.Matrices

import Catlab.Sheaves: pullback_matrix, FinSetCat

VectSheaf = Sheaf(DiagramTopology(), FVectPullback)
VectSheafMat = Sheaf(DiagramTopology(), FMatPullback)

f = FinFunction([1,2], 3)
g = FinFunction([1,2], 3)

@test implements(FinSetC(), ThCategory)
@test implements(FinVect(), ThCategory)

@test hom_map(FVectPullback, FinFunction([1,2,2],4))(1:4) == [1,2,2]

@test pullback_matrix(FinFunction([1,2,2], 4)) == [1 0 0 0; 0 1 0 0; 0 1 0 0]
@test ob_map(FMatPullback, FinSetInt(3)) == 3
@test hom_map(FMatPullback, FinFunction([1,2,2], 4)) == [1 0 0 0; 0 1 0 0; 0 1 0 0]
S = ColimCover(pushout[SkelFinSet()](f,g))

extend(VectSheaf, S, [[1.0, 2,3], [1,2.0,6]])
@test_throws MatchingError extend(VectSheaf, S, [[1.0, 2,3], [1,3.0,6]])
# extend(VectSheaf, S, [[1.0, 2,3], [1,3.0,6]])

D = FreeGraph(FinSetInt.([3,2,3]), # list of objects
 [ # list of (hom, src, tgt) tuples
  (FinFunction([1,2], 3), 2,1),
  (FinFunction([1,2], 3), 2,3),
  ]; cat=SkelFinSet()
) |> FreeDiagram

K = ColimCover(D)

section_data = [Float64[1,2,3],
   Float64[1,2],
   Float64[1,2,5]]

v = extend(VectSheaf, K, section_data)

global_section = extend(VectSheafMat, K, section_data)
@test v == global_section

section_data_bad = [Float64[1,2,3],
   Float64[1,2],
   Float64[1,3,5]]
@test_throws MatchingError extend(VectSheaf, K, section_data_bad)
@test_throws MatchingError extend(VectSheafMat, K, section_data_bad)

# if we disable the checks, VectSheafMat will solve a least squares problem 
# instead of last write wins.
@test extend(VectSheafMat, K, section_data_bad, check=false
            ) != extend(VectSheaf, K, section_data_bad, check=false) 

end # module
