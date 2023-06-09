module TestTheories
using Test

using Catlab.GATs, Catlab.Theories

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr; all::Bool=false) =
  all ? sprint(show, MIME("text/plain"), expr) : sprint(show_unicode, expr)
latex(expr::GATExpr; all::Bool=false) =
  all ? sprint(show, MIME("text/latex"), expr) : sprint(show_latex, expr)

@testset "Categories" begin
  include("Category.jl")
end

@testset "MonoidalCategories" begin
  include("Monoidal.jl")
  include("MonoidalAdditive.jl")
end

@testset "HigherCategories" begin
  include("HigherCategory.jl")
end

@testset "Preorders" begin
  include("Preorders.jl")
end

@testset "Schemas" begin
  include("Schema.jl")
end

end
