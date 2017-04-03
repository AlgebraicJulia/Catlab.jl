module Doctrine
import ..Syntax: BaseExpr

export CategoryExpr, ObExpr, HomExpr, Hom2Expr

# TODO: Generate these automatically from signature?
export Category, FreeCategory, id, compose, ∘, dom, codom
export Category2, FreeCategory2, compose2
export MonoidalCategory, otimes, munit, ⊗
export SymmetricMonoidalCategory, FreeSymmetricMonoidalCategory, braid
export CartesianCategory, FreeCartesianCategory, mcopy, delete
export CocartesianCategory, FreeCocartesianCategory, mmerge, create
export CompactClosedCategory, FreeCompactClosedCategory, dual, ev, coev
export DaggerCategory, DaggerCompactCategory, FreeDaggerCompactCategory, dagger

abstract CategoryExpr{T} <: BaseExpr{T}
abstract ObExpr{T} <: CategoryExpr{T}
abstract HomExpr{T} <: CategoryExpr{T}
abstract Hom2Expr{T} <: CategoryExpr{T}

include("doctrine/Category.jl")
include("doctrine/Monoidal.jl")
include("doctrine/Relations.jl")

end
