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
  h::Hom(W,Z)
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

diagram = @parse_wiring_diagram C (x::X) begin
  f(x)
end
@test diagram == to_wiring_diagram(f)

diagram = @parse_wiring_diagram C (x::X) begin
  g(f(x))
end
@test diagram == to_wiring_diagram(compose(f,g))

diagram = @parse_wiring_diagram C (x::X) begin
  y = f(x)
  z = g(y)
  return z
end
@test diagram == to_wiring_diagram(compose(f,g))

diagram = @parse_wiring_diagram C (x::X, y::Y) begin
  w, z = m(x, y)
  x2, y2 = n(w, z)
  return (x2, y2)
end
@test diagram == to_wiring_diagram(compose(m,n))

diagram = @parse_wiring_diagram C (x::X, y::Y) begin
  n(m(x,y))
end
@test diagram == to_wiring_diagram(compose(m,n))

I = munit(FreeCartesianCategory.Ob)
c = add_generator!(C, Hom(:c, I, X))
d = add_generator!(C, Hom(:d, X, I))

diagram = @parse_wiring_diagram C () begin
  c()
end
@test diagram == to_wiring_diagram(c)

diagram = @parse_wiring_diagram C (x::X) begin
  d(x)
  c()
end
@test diagram == to_wiring_diagram(compose(d,c))

diagram = @parse_wiring_diagram C (x::X) begin
  c(d(x))
end
@test diagram == to_wiring_diagram(compose(d,c))

end
