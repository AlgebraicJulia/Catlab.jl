module Doctrines
export CategoryExpr, ObExpr, HomExpr, Hom2Expr

using ..Catlab
import ..Syntax: GATExpr, show_unicode, show_latex

# Base types for expressions in a category.
abstract type CategoryExpr{T} <: GATExpr{T} end
abstract type ObExpr{T} <: CategoryExpr{T} end
abstract type HomExpr{T} <: CategoryExpr{T} end
abstract type Hom2Expr{T} <: CategoryExpr{T} end

# Convenience methods
Ob(mod::Module, args...) = Ob(mod.Ob, args...)

function Ob(typ::Type, args...)
  if length(args) <= 1
    # Throw an error to avoid infinite recursion.
    # FIXME: Maybe this method should be called `Obs` instead?
    throw(MethodError(Ob, [typ, args...]))
  end
  [ Ob(typ, arg) for arg in args ]
end

include("Category.jl")
include("Monoidal.jl")
include("Preorders.jl")
include("AdditiveMonoidal.jl")
include("Relations.jl")

include("Permutations.jl")

end
