module TestJuliaPrograms

using Test

using Catlab, Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab.Programs.JuliaPrograms

@present C(FreeCartesianCategory) begin
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

# Compilation
#############

X, Y, f, g, h = generators(C, [:X, :Y, :f, :g, :h])

@test compile(f) isa Function
@test compile(compose(f,g)) isa Function
@test compile(otimes(f,h)) isa Function
@test compile(compose(f, mcopy(Y), otimes(g,g))) isa Function

# Parsing
#########

f, g, m, n = generators(C, [:f, :g, :m, :n])

diagram = @parse_wiring_diagram(C, (x::X) -> f(x))
@test diagram == to_wiring_diagram(f)

diagram = @parse_wiring_diagram(C, (x::X) -> g(f(x)))
@test diagram == to_wiring_diagram(compose(f,g))

diagram = @parse_wiring_diagram C (x::X) begin
  y = f(x)
  z = g(y)
  return z
end
@test diagram == to_wiring_diagram(compose(f,g))

diagram = @parse_wiring_diagram C (v::X) begin
  v = f(v)
  v = g(v)
  v = h(v)
  v
end
@test is_permuted_equal(diagram, to_wiring_diagram(compose(f,g,h)), [2,3,1])

diagram = @parse_wiring_diagram C (x::X, y::Y) begin
  w, z = m(x, y)
  x2, y2 = n(w, z)
  return (x2, y2)
end
@test diagram == to_wiring_diagram(compose(m,n))

diagram = @parse_wiring_diagram(C, (x::X, y::Y) -> n(m(x,y)))
@test diagram == to_wiring_diagram(compose(m,n))

I = munit(FreeCartesianCategory.Ob)
c = add_generator!(C, Hom(:c, I, X))
d = add_generator!(C, Hom(:d, X, I))

diagram = @parse_wiring_diagram(C, () -> c())
@test diagram == to_wiring_diagram(c)

diagram = @parse_wiring_diagram(C, (x::X) -> c(d(x)))
@test diagram == to_wiring_diagram(compose(d,c))

diagram = @parse_wiring_diagram C (x::X) begin
  d(x)
  c()
end
@test diagram == to_wiring_diagram(compose(d,c))

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
test_roundtrip(compose(f,g))
test_roundtrip(otimes(f,h))
test_roundtrip(compose(m,n))
test_roundtrip(compose(l, braid(Y,X), m))
test_roundtrip(compose(mcopy(X), otimes(f,f)))

f = compose(f, mcopy(Y), otimes(g,g))
@test is_permuted_equal(roundtrip(f), to_wiring_diagram(f), [2,3,1])

end
