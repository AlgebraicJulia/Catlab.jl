""" Catlab's standard library of generalized algebraic theories.

The focus is on categories and monoidal categories, but other related structures
are also included.
"""
module Theories
export CategoryExpr, ObExpr, HomExpr

using ..Catlab
import ..Syntax: GATExpr, show_unicode, show_latex

# Base types for expressions in a category.
abstract type CategoryExpr{T} <: GATExpr{T} end
abstract type ObExpr{T} <: CategoryExpr{T} end
abstract type HomExpr{T} <: CategoryExpr{T} end

# Convenience methods
Ob(mod::Module, args...) = Ob(mod.Ob, args...)
Ob(typ::Type, x1, x2, args...) = [Ob(typ, arg) for arg in [x1; x2; args...]]

include("Category.jl")
include("Limits.jl")
include("Monoidal.jl")
include("MonoidalAdditive.jl")
include("MonoidalMultiple.jl")
include("IndexedCategory.jl")
include("HigherCategory.jl")
include("Preorders.jl")
include("Relations.jl")
include("Schema.jl")

end
