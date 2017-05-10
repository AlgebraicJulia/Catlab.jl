module Catlab
export @optional_import

using Match
using Reexport

macro optional_import(expr)
  pkg = @match expr begin
    Expr(:using, [name, _...], _) => name
    Expr(:import, [name, _...], _) => name
    Expr(:importall, [name, _...], _) => name
    Expr(:toplevel, [Expr(:using, [name, _...], _), _...], _) => name
    Expr(:toplevel, [Expr(:import, [name, _...], _), _...], _) => name
  end
  cond = :(Pkg.installed($(string(pkg))) != nothing)
  esc(Expr(:toplevel, Expr(:if, cond, expr)))
end

# Core modules
include("GAT.jl")
include("Syntax.jl")
include("Rewrite.jl")

@reexport using .GAT
@reexport using .Syntax
@reexport using .Rewrite

# Additional modules
include("Doctrine.jl")
include("Diagram.jl")
include("Algebra.jl")

end
