# # Basic Sheaf Constructions
# This example shows how to use a sheaf Catlab.
# We use the DiagramTopology on FinSet and the Free Vector Space functor
# to illustrate this process.

using Test
using Catlab.CategoricalAlgebra, Catlab.BasicSets
using Catlab.CategoricalAlgebra.Categories
using Catlab.Sheaves
using Catlab.CategoricalAlgebra.Misc.Matrices: MatrixDom
import Catlab.Sheaves: pullback_matrix, FinSetCat

# The Topology that we are using is the `DiagramTopology`, which says that a cover of an object `c` is any diagram with `c` as its colimit.
# The cocone of the diagram gives you a basis for the sieve that covers `c`.
# The legs of the cocone can be interpreted as open subsets of `c` whose union is `c`.
# Because colimits are functorial and the base category is adhesive, the diagram topology is well defined.
#
# We have two different implementations of equivalent sheaves.
# The `VectSheaf` implementation uses julia functions and the `VectSheafMat` implementation uses sparse matrices.

VectSheaf = Sheaf(DiagramTopology(), FVectPullback)
VectSheafMat = Sheaf(DiagramTopology(), FMatPullback)

# We want to introduce a cover of the set ${1...4}$ with two open sets ${1,2,3}$ and ${1,2,4}$.
# To do that, we will construct a pushout.
f = FinFunction([1,2], 3)
g = FinFunction([1,2], 3)
S = ColimCover(pushout[SkelFinSet()](f,g))

# The main API of a sheaf is that you can:
# 1. restrict sections along a morphism,
# 1. check if a collection of local sections match on the overlaps,
# 1. and extend a collection of local sections if they match.

# We can restrict a global section along the first leg
v = [1,2,3,4]
v₁ = restrict(VectSheaf, v, legs(S)[1])

# Or the second leg.
v₂ = restrict(VectSheaf, v, legs(S)[2])

# Notice that we got two different values, but that the first two entries of those restricted vectors agree.
# That is because our two legs have an overlap in the first two dimensions.
# If we restrict again by the arrows in our diagram (f,g) we should get the same answer.

restrict(VectSheaf, v₁, f)  == restrict(VectSheaf, v₂, g)

# A sheaf requires:
# - a notion of dividing up a space into pieces (the open coverage),
# - a way of measuring data over the pieces (the set of sections given by the functor on objects), along with
# - ways of relating measurements on a piece to measurements on a subpiece (the restriction maps given by the functor).
# Functoriality of the the sheaf tells you that restricting the same data
# along commuting paths will always give you the same data on the common piece.

# The sheaf condition requires that you can compute an extension of local data to global data.
# There is no way to derive this operation from the contravariant functor of the sheaf
# so providing it is part of the API in defining a new sheaf.
extend(VectSheaf, S, [[1.0, 2,3], [1,2.0,6]])

# If the local sections don't match, then extending will fail.
@test_throws MatchingError extend(VectSheaf, S, [[1.0, 2,3], [1,3.0,6]])
# extend(VectSheaf, S, [[1.0, 2,3], [1,3.0,6]])

# Pushouts are the covers with only two subobjects, but the sheaf works on diagrams of any size.

D = FreeDiagram(FreeGraph(FinSet.([3,2,3,3]), # list of objects
 [ # list of (hom, src, tgt) tuples
  (FinFunction([1,2], 3), 2,1),
  (FinFunction([1,2], 3), 2,3),
  (FinFunction([1,2], 3), 2,4)
  ]
))

K = ColimCover(D)

section_data = [Float64[1,2,3],
   Float64[1,2],
   Float64[1,2,5],
   Float64[1,2,6]]

v = extend(VectSheaf, K, section_data)

# Our two sheaves should agree, because they are just two different implementations of the same sheaf.

global_section = extend(VectSheafMat, K, section_data)
v == global_section

# If you put in bad data, you get MatchingErrors
section_data_bad = [Float64[1,2,3],
   Float64[1,2],
   Float64[1,3,5],
   Float64[1,3,6]]

@test_throws MatchingError extend(VectSheaf, K, section_data_bad)
@test_throws MatchingError extend(VectSheafMat, K, section_data_bad)

# if we disable the checks, VectSheafMat will solve a least squares problem instead of last write wins.
extend(VectSheafMat, K, section_data_bad, check=false)

# Last write wins definition is different.
extend(VectSheaf, K, section_data_bad, check=false) 

# You can diagnose a matching error from the exception that extend throws.
try
  extend(VectSheaf, K, section_data_bad)
catch e
  e
end

# This concludes our discussion of the sheaf API.