using Catlab.LinearAlgebra.GraphicalLinearAlgebra, DaggerInstanceGLA, Catlab, Catlab.Doctrines

V, W = Ob(FreeLinearFunctions, :V, :W)
f, g, h = Hom(:f, V, W), Hom(:g, V, W), Hom(:h, W, W)

fop = MatrixThunk(LinearMap([1 1 1 1; 2 2 2 3; 3 3 3 3.0]))
gop = MatrixThunk(LinearMap([3 1 1 1; -1 -1 -1 -1; 0 2 0 0.0]))
hop = MatrixThunk(LinearMap([1 4 -1; -1 1 0; 1 1 -1.0]))

#fop = LinearMap([1 1 1 1; 2 2 2 3; 3 3 3 3.0])
#gop = LinearMap([3 1 1 1; -1 -1 -1 -1; 0 2 0 0.0])
#hop = LinearMap([1 4 -1; -1 1 0; 1 1 -1.0])


d = Dict(f=>fop, g=>gop, h => hop, V => DagDom(4), W=>DagDom(3))
F(ex) = functor((DagDom, MatrixThunk), ex, generators=d)
#d = Dict(f=>fop, g=>gop, h => hop, V => LinearMapDom(4), W=>LinearMapDom(3))
#F(ex) = functor((LinearMapDom, LinearMap), ex, generators=d)

M = plus(f,g)⋅h

print(Matrix(collect(F(M).thunk)))
print('\n')
