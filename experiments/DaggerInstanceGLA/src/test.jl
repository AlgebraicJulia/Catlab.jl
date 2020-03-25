using Catlab.LinearAlgebra.GraphicalLinearAlgebra, DaggerInstanceGLA, Catlab, Catlab.Doctrines
V, W = Ob(FreeLinearFunctions, :V, :W)
f, g, h = Hom(:f, V, W), Hom(:g, V, W), Hom(:h, W, W)
fop = MatrixThunk(matrixToThunk(LinearMap([1 1 1 1; 2 2 2 3; 3 3 3 3.0])), 4,3)
gop = MatrixThunk(matrixToThunk(LinearMap([3 1 1 1; -1 -1 -1 -1; 0 2 0 0.0])), 4,3)
hop = MatrixThunk(matrixToThunk(LinearMap([1 4 -1; -1 1 0; 1 1 -1.0])), 3,3)
d = Dict(f=>fop, g=>gop, h => hop, V => DagDom(4), W=>DagDom(3))
F(ex) = functor((DagDom, MatrixThunk), ex, generators=d)
M = plus(f,g)⋅h

F(M)
