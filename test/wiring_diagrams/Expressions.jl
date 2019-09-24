module TestWiringDiagramExpressions

using Test
using LightGraphs

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.WiringDiagrams.WiringDiagramExpressions: find_parallel,
  find_series, transitive_reduction!

# Expression -> Diagram
#######################

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f, g = Hom(:f,A,B), Hom(:g,B,C)

# Functorality of conversion.
fd, gd = singleton_diagram(Box(f)), singleton_diagram(Box(g))
@test to_wiring_diagram(f) == fd
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(munit(FreeSymmetricMonoidalCategory.Ob)) == munit(Ports)

# Diagram -> Expression
#######################

function roundtrip(f::HomExpr)
  to_hom_expr(FreeBiproductCategory, to_wiring_diagram(f))
end

A, B, C, D = Ob(FreeBiproductCategory, :A, :B, :C, :D)
I = munit(FreeBiproductCategory.Ob)
f, g, h, k = Hom(:f,A,B), Hom(:g,B,C), Hom(:h,C,D), Hom(:k,D,C)

# Monoidal category
#------------------

# Base case.
@test roundtrip(f) == f

# Series reduction.
@test roundtrip(compose(f,g)) == compose(f,g)
@test roundtrip(compose(f,g,h)) == compose(f,g,h)

# Parallel reduction.
@test roundtrip(otimes(f,g)) == otimes(f,g)
@test roundtrip(otimes(f,g,h)) == otimes(f,g,h)

# Series-parallel reduction.
@test roundtrip(otimes(compose(f,g),compose(h,k))) ==
  # roundtrip(compose(otimes(f,h),otimes(g,k))) ==
  otimes(compose(f,g),compose(h,k))
@test roundtrip(otimes(compose(f,g),h)) == otimes(compose(f,g),h)
@test roundtrip(otimes(f,compose(g,h))) == otimes(f,compose(g,h))

m = Hom(:m, otimes(B,B), otimes(C,C))
expr = compose(otimes(f,f),m,otimes(h,h))
@test roundtrip(expr) == expr

m, n = Hom(:m, A, otimes(A,B)), Hom(:n, otimes(B,C), C)
@test roundtrip(compose(m,otimes(f,g),n)) == compose(m,otimes(f,g),n)

m, n = Hom(:m, A, otimes(B,B)), Hom(:n, otimes(B,B), C)
expr = compose(otimes(m,f),otimes(g,n))
@test roundtrip(expr) == expr

m, n = Hom(:m, A, otimes(B,B)), Hom(:n, otimes(C,C), D)
l = Hom(:l, otimes(B,B), otimes(C,C))
expr = compose(otimes(m,m),otimes(g,l,g),otimes(n,n))
@test roundtrip(expr) == expr

# Transitive reduction (necessarily with series and/or parallel reduction).
@test roundtrip(otimes(f,id(C))) == otimes(f,id(C))
@test roundtrip(otimes(id(A),g)) == otimes(id(A),g)

m = Hom(:m, otimes(B,B), otimes(C,C))
expr = compose(otimes(f,id(B)),m,otimes(id(C),h))
@test roundtrip(expr) == expr

m = Hom(:m, otimes(B,B,B), C)
@test roundtrip(compose(otimes(f,id(otimes(B,B))),m)) ==
  compose(otimes(f,id(B),id(B)),m)

m, n = Hom(:m, A, otimes(A,B)), Hom(:n, otimes(B,B), C)
expr = compose(m,otimes(f,id(B)),n)
@test roundtrip(expr) == expr

m = Hom(:m, otimes(A,A), A)
expr = compose(otimes(m,id(otimes(A,A))), otimes(m,id(A)), m)
@test roundtrip(expr) == ((((m ⊗ id(A)) ⋅ m) ⊗ id(A)) ⋅ m)

# Identities.
@test roundtrip(id(A)) == id(A)
@test roundtrip(otimes(id(A),id(B))) == id(otimes(A,B))

# Monoidal units.
@test roundtrip(Hom(:m,A,I)) == Hom(:m,A,I)
@test roundtrip(Hom(:m,I,B)) == Hom(:m,I,B)
@test roundtrip(Hom(:m,I,I)) == Hom(:m,I,I)
@test roundtrip(Hom(:m,I,B)⋅Hom(:n,B,I)) == Hom(:m,I,B)⋅Hom(:n,B,I)
@test roundtrip(Hom(:m,A,I)⋅Hom(:n,I,B)) == Hom(:m,A,I)⊗Hom(:n,I,B)
@test roundtrip(Hom(:m,I,I)⊗Hom(:n,I,I)) == Hom(:m,I,I)⊗Hom(:n,I,I)

# Symmetric monoidal category
#----------------------------

# Braidings.
@test roundtrip(braid(A,B)) == braid(A,B)
@test roundtrip(otimes(id(A),braid(B,C))) == otimes(id(A),braid(B,C))

# Diagonals and codiagonals
#--------------------------

# Diagonals.
@test roundtrip(mcopy(A)) == mcopy(A)
@test roundtrip(delete(A)) == delete(A)
@test roundtrip(mcopy(A)⋅(mcopy(A)⊗id(A))) == mcopy(A)⋅(mcopy(A)⊗id(A))
@test roundtrip(mcopy(A)⋅(id(A)⊗mcopy(A))) == mcopy(A)⋅(mcopy(A) ⊗ id(A))
@test roundtrip(mcopy(A⊗B)) == (mcopy(A)⊗mcopy(B))⋅(id(A)⊗braid(A,B)⊗id(B))
@test roundtrip(delete(A⊗B)) == delete(A)⊗delete(B)

# Codiagonals.
@test roundtrip(mmerge(A)) == mmerge(A)
@test roundtrip(create(A)) == create(A)
@test roundtrip((mmerge(A)⊗id(A)⋅mmerge(A))) == (mmerge(A)⊗id(A))⋅mmerge(A)
@test roundtrip((id(A)⊗mmerge(A))⋅mmerge(A)) == (mmerge(A)⊗id(A))⋅mmerge(A)

# Compound morphisms.
@test roundtrip(compose(f,mcopy(B))) == compose(f,mcopy(B))
@test roundtrip(compose(mcopy(A),otimes(f,f))) == compose(mcopy(A),otimes(f,f))
@test roundtrip(compose(f,delete(B))) == compose(f,delete(B))
@test roundtrip(braid(A,B)⋅(mcopy(B)⊗mcopy(A))) == braid(A,B)⋅(mcopy(B)⊗mcopy(A))

# Graph operations
##################

# Parallel compositions in digraph.
graph = DiGraph([Edge(1,2),Edge(2,3),Edge(3,4),Edge(3,5),Edge(4,6),Edge(5,6)])
@test find_parallel(graph) == Dict((3 => 6) => [4,5])

# Series compositions in digraph.
graph = union(DiGraph(10), path_digraph(3))
add_edge!(graph,5,6); add_edge!(graph,8,9); add_edge!(graph,9,10)
@test Set(find_series(graph)) == Set([[1,2,3],[5,6],[8,9,10]])

# Transitive reduction of DAG.
graph = DiGraph([ Edge(1,2),Edge(1,3),Edge(1,4),Edge(1,5),
                  Edge(2,4),Edge(3,4),Edge(3,5),Edge(4,5) ])
transitive_reduction!(graph)
@test graph == DiGraph([Edge(1,2),Edge(1,3),Edge(2,4),Edge(3,4),Edge(4,5)])

end
