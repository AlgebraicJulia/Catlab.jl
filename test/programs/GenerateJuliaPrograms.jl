module TestGenerateJuliaPrograms

using Test

using Catlab, Catlab.Doctrines
using Catlab.Programs.GenerateJuliaPrograms

# Compilation
#############

# Note: Further tests of compilation are provided by the roundtripping
# integration tests in `TestParseJuliaPrograms`.

W, X, Y, Z = Ob(FreeCartesianCategory, :W, :X, :Y, :Z)
f, g, h = Hom(:f, X, Y), Hom(:g, Y, Z), Hom(:h, Z, W)

@test compile(f) isa Function
@test compile(compose(f,g)) isa Function
@test compile(otimes(f,h)) isa Function
@test compile(compose(f, mcopy(Y), otimes(g,g))) isa Function

end
