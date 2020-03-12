module TestDoctrines

using Test
using Catlab.Doctrines
using Catlab.Syntax

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr) = sprint(show_unicode, expr)
latex(expr::GATExpr) = sprint(show_latex, expr)

@testset "Categories" begin
  include("Category.jl")
end

@testset "MonoidalCategories" begin
  include("Monoidal.jl")
  include("AdditiveMonoidal.jl")
end

@testset "Preorders" begin
  include("Preorders.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

end
