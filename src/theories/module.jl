""" Catlab's standard library of generalized algebraic theories.

The focus is on categories and monoidal categories, but other related structures
are also included.
"""
module Theories
export CategoryExpr, ObExpr, HomExpr, ThCategory

using Reexport

import Base: ≤, +, *, inv, zero, join, show, collect, ndims
import AlgebraicInterfaces: dom, codom, compose, id, Ob, ob, Hom, hom, munit,
  mcompose, ocompose, oapply, attr, attrtype

@reexport using GATlab
using GATlab.Stdlib: ThCategory
import GATlab: show_unicode, show_latex

""" Base type for GAT expressions in categories or other categorical structures.

All symbolic expression types exported by `Catlab.Theories` are subtypes of this
abstract type.
"""
abstract type CategoryExpr{T} <: GATExpr{T} end

""" Base type for object expressions in categorical structures.
"""
abstract type ObExpr{T} <: CategoryExpr{T} end

""" Base type for morphism expressions in categorical structures.
"""
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
