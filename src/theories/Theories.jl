""" Catlab's standard library of generalized algebraic theories.

The focus is on categories and monoidal categories, but other related structures
are also included.
"""
module Theories
export CategoryExpr, ObExpr, HomExpr, Hom2Expr

using ..Catlab
import ..Syntax: GATExpr, show_unicode, show_latex

# Base types for expressions in a category.
abstract type CategoryExpr{T} <: GATExpr{T} end
abstract type ObExpr{T} <: CategoryExpr{T} end
abstract type HomExpr{T} <: CategoryExpr{T} end
# 2-categories and double categories
abstract type Hom2Expr{T} <: CategoryExpr{T} end
# double categories
abstract type HomVExpr{T} <: CategoryExpr{T} end
abstract type HomHExpr{T} <: CategoryExpr{T} end

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
include("Limits.jl")
include("Monoidal.jl")
include("MonoidalAdditive.jl")
include("MonoidalMultiple.jl")
include("Preorders.jl")
include("Relations.jl")
include("Schema.jl")

end
