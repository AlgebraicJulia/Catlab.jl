module TestWiringDiagramAlgebras
using Test

using Tables, TypedTables

using Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
using Catlab.Graphs, Catlab.WiringDiagrams, Catlab.Programs.RelationalPrograms

tuples(args...) = sort!(collect(zip(args...)))

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
@test tuples(src(k0), tgt(k0)) == [(1,2), (2,3), (2,4), (3,5), (4,5), (5,6)]
@test [ collect(leg[:V]) for leg in legs(k) ] == [[1], [6]]

# Parallel composition.
para = @relation (a,c,b,d) where (a,b,c,d) begin
  g(a,b)
  h(c,d)
end
k = oapply(para, Dict(:g => g, :h => h))
@test length(legs(k)) == 4
@test feet(k) == [first(feet(g)), first(feet(h)), last(feet(g)), last(feet(h))]
k0 = apex(k)
@test (nv(k0), ne(k0)) == (8, 6)
@test tuples(src(k0), tgt(k0)) == [(1,2), (2,3), (2,4), (5,7), (6,7), (7,8)]
@test [ collect(leg[:V]) for leg in legs(k) ] == [[1], [5,6], [3,4], [8]]

# Identity for sequential composition.
seq_id = @relation (a,a) where (a,) begin end
k = oapply(seq_id, Dict{Symbol,OpenGraph}(), Dict(:a => FinSet(3)))
@test apex(k) == Graph(3)
@test feet(k) == [FinSet(3), FinSet(3)]

# Queries of ACSets
###################

# Query: directed paths of length 2.
paths2 = @relation (start=start, stop=stop) begin
  E(src=start, tgt=mid)
  E(src=mid, tgt=stop)
end
count_paths2 = @relation (;) begin
  E(src=start, tgt=mid)
  E(src=mid, tgt=stop)
end

# Graph underlying a commutative squares.
square = Graph(4)
add_edges!(square, [1,1,2,3], [2,3,4,4])
result = query(square, paths2)
@test result == Table((start=[1,1], stop=[4,4]))

# Graph underlying a pasting of two commutative squares.
squares2 = copy(square)
add_vertices!(squares2, 2)
add_edges!(squares2, [2,4,5], [5,6,6])
result = query(squares2, paths2)
@test tuples(columns(result)...) == [(1,4), (1,4), (1,5), (2,6), (2,6), (3,6)]
@test length(query(squares2, count_paths2)) == 6

result = query(squares2, paths2, (start=1,))
@test tuples(columns(result)...) == [(1,4), (1,4), (1,5)]
result = query(squares2, paths2, (start=1, stop=4))
@test result == Table((start=[1,1], stop=[4,4]))
@test length(query(squares2, count_paths2, (start=1, stop=4))) == 2

# Query: pairs of vertices.
vertices2 = @relation (v1=v1, v2=v2) begin
  V(_id=v1)
  V(_id=v2)
end
@test length(query(squares2, vertices2)) == nv(squares2)^2

# Query: directed cycles of length 3.
cycles3 = @relation (edge1=e, edge2=f, edge3=g) where (e,f,g,u,v,w) begin
  E(_id=e, src=u, tgt=v)
  E(_id=f, src=v, tgt=w)
  E(_id=g, src=w, tgt=u)
end

# Cycle graph.
g = cycle_graph(Graph, 3)
result = query(g, cycles3)
@test tuples(columns(result)...) == [(1,2,3), (2,3,1), (3,1,2)]
result = query(g, cycles3, (v=1,))
@test result == Table((edge1=[3], edge2=[1], edge3=[2]))
@test isempty(query(cycle_graph(Graph, 4), cycles3))

end
