module Doctrine
export CategoryExpr, ObExpr, HomExpr, Hom2Expr

# TODO: Generate these automatically from signature?
export Category, FreeCategory, ob, hom, dom, codom, id, compose, ∘
export Category2, FreeCategory2, hom2, compose2

export MonoidalCategory, otimes, munit, ⊗, collect, ndims
export SymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid
export CartesianCategory, FreeCartesianCategory, mcopy, delete,
  pair, proj1, proj2, Δ, ◇
export CocartesianCategory, FreeCocartesianCategory, mmerge, create,
  copair, in1, in2, ∇, □
export BiproductCategory, FreeBiproductCategory
export CompactClosedCategory, FreeCompactClosedCategory, dual, ev, coev
export DaggerCategory, FreeDaggerCategory, dagger
export DaggerCompactCategory, FreeDaggerCompactCategory

export BicategoryRelations, FreeBicategoryRelations
export AbelianBicategoryRelations, FreeAbelianBicategoryRelations,
  plus, coplus, zero, cozero

using ..Catlab
import ..Syntax: BaseExpr, show_unicode, show_latex

# Base types for expressions in a category.
abstract type CategoryExpr{T} <: BaseExpr{T} end
abstract type ObExpr{T} <: CategoryExpr{T} end
abstract type HomExpr{T} <: CategoryExpr{T} end
abstract type Hom2Expr{T} <: CategoryExpr{T} end

# Convenience methods
ob(mod::Module, args...) = ob(mod.Ob, args...)

function ob(typ::Type, args...)
  if length(args) <= 1
    # Throw an error to avoid infinite recursion.
    # FIXME: Maybe this method should be called `obs` instead?
    throw(MethodError(ob, [typ, args...]))
  end
  [ ob(typ, arg) for arg in args ]
end

include("Category.jl")
include("Monoidal.jl")
include("Relations.jl")

end
