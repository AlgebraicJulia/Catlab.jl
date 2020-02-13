module TestTikZWiringDiagrams

using Compat
using Test

using Catlab.Doctrines, Catlab.WiringDiagrams
using Catlab: Graphics
using Catlab.Graphics: TikZ

to_tikz(f; kw...) = Graphics.to_tikz(f; outer_ports_layout=:fixed, kw...)

function stmts(expr::TikZ.Expression, type::Type)
  children = hasfield(typeof(expr), :stmts) ? expr.stmts : []
  vcat(expr isa type ? [expr] : [],
       mapreduce(expr -> stmts(expr, type), vcat, children; init=[]))
end
stmts(doc::TikZ.Document, type::Type) = stmts(doc.picture, type)

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

pic = to_tikz(f)
@test length(stmts(pic, TikZ.Node)) == 2 # Includes outer box
@test length(stmts(pic, TikZ.Edge)) == 2

pic = to_tikz(id(A))
@test length(stmts(pic, TikZ.Node)) == 1
@test length(stmts(pic, TikZ.Edge)) == 1

pic = to_tikz(compose(f,g))
@test length(stmts(pic, TikZ.Node)) == 3
@test length(stmts(pic, TikZ.Edge)) == 3

pic = to_tikz(otimes(f,g))
@test length(stmts(pic, TikZ.Node)) == 3
@test length(stmts(pic, TikZ.Edge)) == 4

pic = to_tikz(braid(A,B))
@test length(stmts(pic, TikZ.Node)) == 1
@test length(stmts(pic, TikZ.Edge)) == 2

A, B = Ob(FreeBiproductCategory, :A, :B)

for expr in (mcopy(A), delete(A), mmerge(A), create(A))
  pic = to_tikz(expr)
  @test length(stmts(pic, TikZ.Node)) == 2
end

end
