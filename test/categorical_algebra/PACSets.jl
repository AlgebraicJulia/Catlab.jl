module TestPACSets

using Test
using Catlab.Theories, Catlab.Present, Catlab.CategoricalAlgebra.PACSets

@present TheoryMatrixGraph(FreeMonoidalSchema) begin
  V::Ob
  EdgeTy::AttrType
  edges::Attr(V ⊗ V, EdgeTy)
end

@pacset_type MatrixGraph(TheoryMatrixGraph)

# Intelligently set the number of vertices based on the edge matrix
g = MatrixGraph{Bool}(edges = Bool[0 1 1; 0 0 1; 0 0 0])

@test nparts(g, :V) == 3
@test subpart(g, :edges) == Bool[0 1 1; 0 0 1; 0 0 0]

# Won't accept a non-square matrix
@test_throws AssertionError MatrixGraph{Bool}(edges = Bool[0 0 0])

end

