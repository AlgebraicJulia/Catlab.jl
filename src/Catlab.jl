__precompile__()

module Catlab
export @optional_import

import Pkg
using Match
using Reexport

macro optional_import(expr)
  pkg = @match expr begin
    Expr(:using, [name, _...]) => name
    Expr(:import, [name, _...]) => name
    Expr(:toplevel, [Expr(:using, [name, _...]), _...]) => name
    Expr(:toplevel, [Expr(:import, [name, _...]), _...]) => name
  end
  cond = :(haskey($(GlobalRef(Pkg, :installed))(), $(string(pkg))))
  esc(Expr(:toplevel, Expr(:if, cond, expr)))
end

# Core modules
include("Meta.jl")
include("GAT.jl")
include("Syntax.jl")
include("Rewrite.jl")
include("Present.jl")

@reexport using .GAT
@reexport using .Syntax
@reexport using .Rewrite
@reexport using .Present

# Additional modules
include("doctrine/Doctrine.jl")
include("diagram/Diagram.jl")
include("algebra/Algebra.jl")

end
