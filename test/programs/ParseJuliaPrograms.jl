module TestParseJuliaPrograms

using Test

using Catlab, Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Programs
using Catlab.Programs.ParseJuliaPrograms: normalize_arguments

@present C(FreeBiproductCategory) begin
  W::Ob
  X::Ob
  Y::Ob
  Z::Ob
  f::Hom(X,Y)
  g::Hom(Y,Z)
  h::Hom(Z,W)
  l::Hom(otimes(Z,W),otimes(Y,X))
  m::Hom(otimes(X,Y),otimes(W,Z))
  n::Hom(otimes(W,Z),otimes(X,Y))
end

# Parsing
#########

W, X, Y, Z = generators(C, [:W, :X, :Y, :Z])
f, g, h, m, n = generators(C, [:f, :g, :h, :m, :n])

# Generator.

parsed = @program(C, (x::X) -> f(x))
@test parsed == to_wiring_diagram(f)
@test parsed isa WiringDiagram{BiproductCategory.Hom}

# Composition: one-dimensional.

parsed = @program(C, (x::X) -> g(f(x)))
@test parsed == to_wiring_diagram(compose(f,g))

parsed = @program C (x::X) begin
  y = f(x)
  z = g(y)
  return z
end
@test parsed == to_wiring_diagram(compose(f,g))

parsed = @program C (v::X) begin
  v = f(v)
  v = g(v)
  v = h(v)
  v
end
@test parsed == to_wiring_diagram(compose(f,g,h))

# Composition: multidimensional.

parsed = @program C (x::X, y::Y) begin
  w, z = m(x, y)
  x2, y2 = n(w, z)
  return (x2, y2)
end
@test parsed == to_wiring_diagram(compose(m,n))

parsed = @program(C, (x::X, y::Y) -> n(m(x,y)))
@test parsed == to_wiring_diagram(compose(m,n))

# Constants and co-constants.

I = munit(FreeBiproductCategory.Ob)
c = add_generator!(C, Hom(:c, I, X))
d = add_generator!(C, Hom(:d, X, I))

parsed = @program(C, () -> c())
@test parsed == to_wiring_diagram(c)

parsed = @program(C, (x::X) -> c(d(x)))
@test parsed == to_wiring_diagram(compose(d,c))

parsed = @program C (x::X) begin
  d(x)
  c()
end
@test parsed == to_wiring_diagram(compose(d,c))

# Diagonals: implicit syntax.

parsed = @program(C, (x::X) -> (f(x),f(x)))
@test parsed == to_wiring_diagram(compose(mcopy(X),otimes(f,f)))

parsed = @program(C, (x::X) -> nothing)
@test parsed == to_wiring_diagram(delete(X))

# Codiagonals: special syntax.

parsed = @program(C, (x1::X, x2::X) -> f([x1,x2]))
@test parsed == to_wiring_diagram(compose(mmerge(X),f))

parsed = @program(C, (x1::X, x2::X) -> [f(x1),f(x2)])
@test parsed == to_wiring_diagram(compose(otimes(f,f),mmerge(Y)))

parsed = @program(C, (x::X, y::Y) -> n([m(x,y), m(x,y)]))
@test parsed == to_wiring_diagram(compose(
  mcopy(otimes(X,Y)), otimes(m,m), mmerge(otimes(W,Z)), n))

parsed = @program(C, () -> f([]))
@test parsed == to_wiring_diagram(compose(create(X),f))

# Explicit syntax for special objects and morphisms.

parsed = @program(C, (x::X) -> id{X}(x))
@test parsed == to_wiring_diagram(id(X))

parsed = @program(C, (x::X) -> mcopy{X}(x))
@test parsed == to_wiring_diagram(mcopy(X))

parsed = @program(C, (x::X) -> delete{X}(x))
@test parsed == to_wiring_diagram(delete(X))

parsed = @program(C, (x1::X, x2::X) -> mmerge{X}(x1,x2))
@test parsed == to_wiring_diagram(mmerge(X))

parsed = @program(C, () -> create{X}())
@test parsed == to_wiring_diagram(create(X))

parsed = @program(C, (x::X, y::Y) -> mcopy{otimes{X,Y}}(x,y))
@test parsed == to_wiring_diagram(mcopy(otimes(X,Y)))

parsed = @program(C, (x::X, y::Y) -> delete{otimes{X,Y}}(x,y))
@test parsed == to_wiring_diagram(delete(otimes(X,Y)))

parsed = @program(C, (x::X) -> Δ{X}(x))
@test parsed == to_wiring_diagram(mcopy(X))

parsed = @program(C, (x1::X, x2::X) -> ∇{X}(x1,x2))
@test parsed == to_wiring_diagram(mmerge(X))

parsed = @program(C, (xy::otimes{X,Y}) -> m(xy))
@test parsed == to_wiring_diagram(m)

parsed = @program C (xy::otimes{X,Y}) begin
  x, y = xy
  (f(x), g(y))
end
@test parsed == to_wiring_diagram(otimes(f,g))

parsed = @program(C, (xy::otimes{X,Y}, wz::otimes{W,Z}) -> (m(xy), n(wz)))
@test parsed == to_wiring_diagram(otimes(m,n))

# Helper function: normalization of arguments.

normalize(args...) = normalize_arguments(Tuple(args))

@test normalize(nothing) == ()
@test normalize(1) == ([1],)
@test normalize(1,nothing,2) == ([1],[2])
@test normalize(1,2,3) == ([1],[2],[3])
@test normalize((1,2,3)) == ([1],[2],[3])
@test normalize((1,2),3) == ([1],[2],[3])
@test normalize(((1,2),3)) == ([1],[2],[3])

@test normalize([]) == ([],)
@test normalize([1]) == ([1],)
@test normalize([1,2]) == ([1,2],)
@test normalize([1,2],[3,4]) == ([1,2],[3,4])
@test normalize([(1,2),(3,4)]) == ([1,3],[2,4])
@test normalize([[(1,2),(3,4)],(5,6)]) == ([1,3,5],[2,4,6])

# Roundtrip
###########

""" Convert morphism expression to Julia code and then back to wiring diagram.
"""
function roundtrip(f::HomExpr)::WiringDiagram
  expr = compile_expr(f, arg_types=first.(collect(dom(f))))
  parse_wiring_diagram(C, expr)
end

function test_roundtrip(f::HomExpr)
  @test roundtrip(f) == to_wiring_diagram(f)
end

f, g, h, l, m, n = generators(C, [:f, :g, :h, :l, :m, :n])

test_roundtrip(f)
test_roundtrip(id(X))
test_roundtrip(compose(f,g))
test_roundtrip(otimes(f,h))
test_roundtrip(compose(m,n))
test_roundtrip(compose(l, braid(Y,X), m))
test_roundtrip(compose(mcopy(X), otimes(f,f)))
test_roundtrip(compose(f, mcopy(Y), otimes(g,g)))

end
