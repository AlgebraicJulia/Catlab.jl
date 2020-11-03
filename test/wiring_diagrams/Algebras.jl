module TestWiringDiagramAlgebras
using Test

using Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using Catlab.Graphs, Catlab.WiringDiagrams, Catlab.Programs.RelationalPrograms

# UWD algebra of structured multicospans
########################################

const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)

# Directed fork as open graph with one input and two outputs.
g0 = Graph(4)
add_edges!(g0, [1,2,2], [2,3,4])
g = OpenGraph(g0, FinFunction([1],4), FinFunction([3,4],4))

# Opposite of previous graph.
h0 = Graph(4)
add_edges!(h0, [1,2,3], [3,3,4])
h = OpenGraph(h0, FinFunction([1,2],4), FinFunction([4],4))

# Sequential composition.
seq = @relation (a,c) where (a,b,c) begin
  g(a,b)
  h(b,c)
end
k = oapply(seq, Dict(:g => g, :h => h))
@test length(legs(k)) == 2
@test feet(k) == [first(feet(g)), last(feet(h))]
k0 = apex(k)
@test (nv(k0), ne(k0)) == (6, 6)
@test sort!(collect(zip(src(k0), tgt(k0)))) == sort!(
  [(3,1), (1,4), (1,5), (4,2), (5,2), (2,6)])
# [(1,2), (2,3), (2,4), (3,5), (4,5), (5,6)]
# Composite graph is isomorphic to that with standard labeling.
@test [ collect(leg[:V]) for leg in legs(k) ] == [[3], [6]]

# Parallel composition.
para = @relation (a,b,c,d) where (a,b,c,d) begin
  g(a,b)
  h(c,d)
end
k = oapply(para, Dict(:g => g, :h => h))
@test length(legs(k)) == 4
@test feet(k) == [feet(g); feet(h)]
k0 = apex(k)
@test (nv(k0), ne(k0)) == (8, 6)

# Identity for sequential composition.
seq_id = @relation (a,a) where (a,) begin end
k = oapply(seq_id, Dict{Symbol,OpenGraph}(), Dict(:a => FinSet(3)))
@test apex(k) == Graph(3)
@test feet(k) == [FinSet(3), FinSet(3)]

end
