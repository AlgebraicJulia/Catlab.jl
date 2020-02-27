module TestWiringDiagramExpressions

using Test
using LightGraphs

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Syntax: syntax_module
using Catlab.WiringDiagrams.WiringDiagramExpressions: find_parallel,
  find_series, transitive_reduction!

# Expression -> Diagram
#######################

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
I = munit(FreeSymmetricMonoidalCategory.Ob)
f, g = Hom(:f,A,B), Hom(:g,B,C)

# Functorality of conversion.
fd, gd = to_wiring_diagram(f), to_wiring_diagram(g)
@test to_wiring_diagram(compose(f,g)) == compose(fd,gd)
@test to_wiring_diagram(otimes(f,g)) == otimes(fd,gd)
@test to_wiring_diagram(I) == munit(Ports)

# Diagram -> Expression
#######################

roundtrip(A::ObExpr) = to_ob_expr(syntax_module(f), to_wiring_diagram(A))
roundtrip(f::HomExpr) = to_hom_expr(syntax_module(f), to_wiring_diagram(f))

# Symmetric monoidal category
#----------------------------

A, B, C, D = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C, :D)
I = munit(FreeSymmetricMonoidalCategory.Ob)
f, g, h, k = Hom(:f,A,B), Hom(:g,B,C), Hom(:h,C,D), Hom(:k,D,C)

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
expr = compose(otimes(m,id(A),id(A)), otimes(m,id(A)), m)
@test roundtrip(expr) == expr

m, n = Hom(:m, A, otimes(B,B)), Hom(:n, otimes(B,B), C)
expr = compose(otimes(m,id(B)), otimes(id(B),n))
@test roundtrip(expr) == expr
b = Hom(:b, B, B)
expr = compose(otimes(m,id(B)), otimes(id(B),b,id(B)), otimes(id(B),n))
@test roundtrip(expr) == expr

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

# Monoidal units with transitive reduction.
@test roundtrip(Hom(:m,A,I)⊗id(B)) == Hom(:m,A,I)⊗id(B)
@test roundtrip(id(A)⊗Hom(:m,I,B)) == id(A)⊗Hom(:m,I,B)
@test roundtrip(id(A)⊗Hom(:m,I,I)) == id(A)⊗Hom(:m,I,I)

expr = compose(id(A)⊗Hom(:m,I,A), Hom(:l, A⊗A, B⊗B), Hom(:n,B,I)⊗id(B))
@test roundtrip(expr) == expr

# Braidings.
@test roundtrip(braid(A,B)) == braid(A,B)
@test roundtrip(otimes(id(A),braid(B,C))) == otimes(id(A),braid(B,C))

# Diagonals and codiagonals
#--------------------------

A, B, C = Ob(FreeBiproductCategory, :A, :B, :C)
f, g = Hom(:f,A,B), Hom(:g,B,C)

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

# Dagger category
#----------------

A, B, C = Ob(FreeDaggerSymmetricMonoidalCategory, :A, :B, :C)
f, g = Hom(:f,A,B), Hom(:g,B,C)

@test roundtrip(dagger(f)) == dagger(f)
@test roundtrip(dagger(compose(f,g))) == compose(dagger(g),dagger(f))

# Compact closed category
#------------------------

A, B, C = Ob(FreeCompactClosedCategory, :A, :B, :C)
f, g = Hom(:f,A,B), Hom(:g,B,C)

# Duals.
@test roundtrip(dual(A)) == dual(A)
@test roundtrip(dual(otimes(A,B))) == otimes(dual(B),dual(A))

# Units and counits.
@test roundtrip(dunit(A)) == dunit(A)
@test roundtrip(dcounit(A)) == dcounit(A)
# TODO: The following expressions are correct, but it would be nice to return
# them in the commented simplified form.
@test roundtrip(dunit(otimes(A,B))) ==
  #dunit(B) ⋅ (id(dual(B)) ⊗ dunit(A) ⊗ id(B))
  (dunit(A) ⊗ dunit(B)) ⋅
    (id(dual(A))⊗braid(A,dual(B))⊗id(B)) ⋅ (braid(dual(A),dual(B))⊗id(A⊗B))
@test roundtrip(dcounit(otimes(A,B))) ==
  #(id(A) ⊗ dcounit(B) ⊗ id(dual(A))) ⋅ dcounit(A)
  (id(A⊗B)⊗braid(dual(B),dual(A))) ⋅ (id(A)⊗braid(B,dual(A))⊗id(dual(B))) ⋅
    (dcounit(A) ⊗ dcounit(B))

# Adjoint mates.
@test roundtrip(mate(f)) == mate(f)
@test roundtrip(mate(compose(f,g))) == compose(mate(g),mate(f))

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
