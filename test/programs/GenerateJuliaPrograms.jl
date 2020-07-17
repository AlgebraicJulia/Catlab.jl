module TestGenerateJuliaPrograms

using Test

using Catlab, Catlab.Theories
using Catlab.Programs.GenerateJuliaPrograms

ℝ = Ob(FreeCartesianCategory, :ℝ)
plus_hom = Hom(:+, ℝ⊗ℝ, ℝ)
cos_hom, sin_hom = Hom(:cos, ℝ, ℝ), Hom(:sin, ℝ, ℝ)

# Compilation
#############

# Note: Further testing of compilation  the roundtripping
# integration tests in `TestParseJuliaPrograms`.

x = collect(range(-2,stop=2,length=50))
@test compile(cos_hom).(x) == cos.(x)
@test compile(compose(cos_hom, sin_hom)).(x) == @. sin(cos(x))
@test compile(otimes(cos_hom, sin_hom))(π/2, π/2) == (cos(π/2), sin(π/2))

# Evaluation
############

generators = Dict{Symbol,Any}(:+ => +, :cos => cos, :sin => sin)
ev = (args...; kw...) -> evaluate(args...; generators=generators, kw...)

# Generators.
x = collect(range(-2,stop=2,length=50))
@test ev(sin_hom, π/2) == sin(π/2)
@test ev(cos_hom, x; broadcast=true) == cos.(x)

# Composition.
@test ev(compose(cos_hom, sin_hom), 1) == sin(cos(1))
@test ev(compose(cos_hom, sin_hom), x; broadcast=true) == sin.(cos.(x))
@test ev(id(ℝ), 1) == 1

# Symmetric monoidal product.
@test ev(otimes(cos_hom, sin_hom), 1, 2) == (cos(1), sin(2))
@test ev(otimes(cos_hom, sin_hom), x, x; broadcast=true) == (cos.(x), sin.(x))
@test ev(braid(ℝ,ℝ), 1, 2) == (2, 1)

# Copying and deleting.
@test ev(mcopy(ℝ), 1) == (1, 1)
@test ev(mcopy(ℝ⊗ℝ), 1, 2) == (1, 2, 1, 2)
@test ev(delete(ℝ), 1) == nothing
@test ev(delete(ℝ⊗ℝ), 1, 2) == nothing

f = compose(mcopy(ℝ), otimes(cos_hom, sin_hom), plus_hom)
@test ev(f, 1) == cos(1) + sin(1)
@test ev(f, x; broadcast=true) == cos.(x) + sin.(x)

end
