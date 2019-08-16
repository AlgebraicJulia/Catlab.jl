module TestDoctrines

using Test
using Catlab.Doctrines
using Catlab.Syntax

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr) = sprint(show_unicode, expr)
latex(expr::GATExpr) = sprint(show_latex, expr)

include("Category.jl")
include("Monoidal.jl")

end
