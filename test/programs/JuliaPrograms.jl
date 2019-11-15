module TestJuliaPrograms

using Test

using Catlab.Doctrines
using Catlab.Programs.JuliaPrograms

X = Ob(FreeCartesianCategory, :X)
f, g, h = Hom(:f, X, X), Hom(:g, X, X), Hom(:h, X, X)

@test compile_expr(f) isa Expr
@test compile_expr(compose(f,g)) isa Expr
@test compile_expr(otimes(f,g)) isa Expr

end
