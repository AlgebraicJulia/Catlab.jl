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

# Evaluation
############

ℝ = Ob(FreeCartesianCategory, :ℝ)

plus, cos_hom, sin_hom = Hom(:+, ℝ⊗ℝ, ℝ), Hom(:cos, ℝ, ℝ), Hom(:sin, ℝ, ℝ)
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

f = compose(mcopy(ℝ), otimes(cos_hom, sin_hom), plus)
@test ev(f, 1) == cos(1) + sin(1)
@test ev(f, x; broadcast=true) == cos.(x) + sin.(x)

end
