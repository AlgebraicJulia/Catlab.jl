module TestJuliaPrograms

using Test

using Catlab.Doctrines
using Catlab.Programs.JuliaPrograms

X = Ob(FreeCartesianCategory, :X)
f, g, h = Hom(:f, X, X), Hom(:g, X, X), Hom(:h, X, X)

@test compile(f) isa Function
@test compile(compose(f,g)) isa Function
@test compile(otimes(f,g)) isa Function
@test compile(compose(f, mcopy(X), otimes(g,h))) isa Function

end
