module TestJuliaPrograms

using Test

using Catlab, Catlab.Doctrines
using Catlab.Programs.JuliaPrograms

@present C(FreeCartesianCategory) begin
  W::Ob
  X::Ob
  Y::Ob
  Z::Ob
  f::Hom(X,Y)
  g::Hom(Y,Z)
  h::Hom(W,Z)
  m::Hom(otimes(X,Y),otimes(W,Z))
  n::Hom(otimes(Z,W),otimes(Y,X))
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

@parse_wiring_diagram C (x::X) begin
  f(x)
end

@parse_wiring_diagram C (x::X) begin
  g(f(x))
end
@parse_wiring_diagram C (x::X) begin
  y = f(x)
  z = g(y)
  return z
end

end
