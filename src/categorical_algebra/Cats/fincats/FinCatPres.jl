module FinCatPres 
export FinCatPresentation, presentation

using StructEquality

using GATlab
import GATlab: equations

using .....Theories: ThCategory, ThSchema, ThPointedSetSchema, AttrTypeExpr 
import .....Theories: hom, id, dom, codom, compose

using ..FinCats 
import ..FinCats: FinCat, ob_generators, hom_generators, ob_generator, 
  hom_generator, ob_generator_name, hom_generator_name

# Symbolic categories
#####################

""" Category defined by a `Presentation` object.

The presentation type can, of course, be a category (`Theories.Category`). It
can also be a schema (`Theories.Schema`). In this case, the schema's objects and
attribute types are regarded as the category's objects and the schema's
morphisms, attributes, and attribute types as the category's morphisms (where
the attribute types are identity morphisms). When the schema is formalized as a
profunctor whose codomain category is discrete, this amounts to taking the
collage of the profunctor.
"""
@struct_hash_equal struct FinCatPresentation{T,Ob,Hom} <: FinCat{Ob,Hom}
  presentation::Presentation{T}
end

function FinCatPresentation(pres::Presentation{T}) where T
  S = pres.syntax
  FinCatPresentation{T,S.Ob,S.Hom}(pres)
end
function FinCatPresentation(pres::Presentation{ThSchema.Meta.T})
  S = pres.syntax
  Ob = Union{S.Ob, S.AttrType}
  Hom = Union{S.Hom, S.Attr, S.AttrType}
  FinCatPresentation{ThSchema.Meta.T,Ob,Hom}(pres)
end

function FinCatPresentation(pres::Presentation{ThPointedSetSchema.Meta.T})
  S = pres.syntax
  Ob = Union{S.Ob, S.AttrType}
  Hom = Union{S.Hom, S.Attr, S.AttrType}
  FinCatPresentation{ThPointedSetSchema.Meta.T,Ob,Hom}(pres)
end

"""
Computes the graph generating a finitely presented category. Ignores any
attribute side and any equations. Optionally returns the mappings from
generators to their indices in the resulting graph.
"""
presentation(C::FinCatPresentation) = C.presentation

ob_generators(C::FinCatPresentation) = generators(presentation(C), :Ob)
ob_generators(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}) = let P = presentation(C)
  vcat(generators(P, :Ob), generators(P, :AttrType))
end

hom_generators(C::FinCatPresentation) = generators(presentation(C), :Hom)
hom_generators(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}) = let P = presentation(C)
  vcat(generators(P, :Hom), generators(P, :Attr))
end
equations(C::FinCatPresentation) = equations(presentation(C))

ob_generator(C::FinCatPresentation, x) = ob(C, presentation(C)[x])
ob_generator(C::FinCatPresentation, x::GATExpr{:generator}) = ob(C, x)
ob_generator_name(C::FinCatPresentation, x::GATExpr{:generator}) = first(x)

hom_generator(C::FinCatPresentation, f) = hom(C, presentation(C)[f])
hom_generator(C::FinCatPresentation, f::GATExpr{:generator}) = hom(C, f)
hom_generator_name(C::FinCatPresentation, f::GATExpr{:generator}) = first(f)

ob(C::FinCatPresentation, x::GATExpr) =
  gat_typeof(x) == :Ob ? x : error("Expression $x is not an object")
ob(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, x::GATExpr) =
  gat_typeof(x) ∈ (:Ob, :AttrType) ? x :
    error("Expression $x is not an object or attribute type")

hom(C::FinCatPresentation, f) = hom_generator(C, f)
hom(C::FinCatPresentation, fs::AbstractVector) =
  mapreduce(f -> hom(C, f), compose, fs)
hom(C::FinCatPresentation, f::GATExpr) =
  gat_typeof(f) == :Hom ? f : error("Expression $f is not a morphism")
hom(::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, f::GATExpr) =
  gat_typeof(f) ∈ (:Hom, :Attr, :AttrType) ? f :
    error("Expression $f is not a morphism or attribute")

id(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, x::AttrTypeExpr) = x
compose(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, f::AttrTypeExpr, g::AttrTypeExpr) =
  (f == g) ? f : error("Invalid composite of attribute type identities: $f != $g")

function Base.show(io::IO, C::FinCatPresentation)
  print(io, "FinCat(")
  show(io, presentation(C))
  print(io, ")")
end

FinCat(pres::Presentation, args...; kw...) =
  FinCatPresentation(pres, args...; kw...)

end # module
