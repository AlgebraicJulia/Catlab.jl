""" Symbolic categories """
module FinCatPres 
export FinCatPresentation

using StructEquality

using GATlab 
import GATlab: equations, getvalue

using ......Theories: ThSchema, ThPointedSetSchema, AttrTypeExpr, FreeSchema
import ......Theories: id, compose, dom, codom
                      
using ......BasicSets: FinSet
using ...Paths: Path
using ..FinCats: ThFinCat
import ..FinCats: FinCat


""" Category defined by a `Presentation` object.

The presentation type can, of course, be a category (`Theories.Category`). It
can also be a schema (`Theories.Schema`). In this case, the schema's objects and
attribute types are regarded as the category's objects and the schema's
morphisms, attributes, and attribute types as the category's morphisms (where
the attribute types are identity morphisms). When the schema is formalized as a
profunctor whose codomain category is discrete, this amounts to taking the
collage of the profunctor.
"""
@struct_hash_equal struct FinCatPresentation{T}
  presentation::Presentation{T}
end

getvalue(f::FinCatPresentation) = f.presentation

# Constructors
#--------------
FinCat(pres::Presentation, args...; kw...) =
  FinCat(FinCatPresentation(pres, args...; kw...))

function FinCatPresentation(pres::Presentation{ThPointedSetSchema.Meta.T})
  S = pres.syntax
  Ob = Union{S.Ob, S.AttrType}
  Hom = Union{S.Hom, S.Attr, S.AttrType}
  FinCatPresentation{ThPointedSetSchema.Meta.T,Ob,Hom}(pres)
end

# Other methods
#-------------

equations(C::FinCatPresentation) = equations(presentation(C))

presentation(C::FinCatPresentation) = C.presentation # synonym for getvalue

# Implementation of FinCat interface
####################################

@instance ThFinCat{GATExpr{:generator}, GATExpr, GATExpr{:generator}, 
                   Path{GATExpr{:generator}, GATExpr}, FinSet
                  } [model::FinCatPresentation{T}] where {T} begin
  src(f::GATExpr{:generator})::GATExpr{:generator} = dom(getvalue(model), f)

  tgt(f::GATExpr{:generator})::GATExpr{:generator} = codom(getvalue(model), f)

  dom(f::GATExpr)::GATExpr{:generator} = dom(getvalue(model), f)

  codom(f::GATExpr)::GATExpr{:generator} = codom(getvalue(model), f)

  id(x::GATExpr{:generator})::GATExpr = id(getvalue(model), x)

  compose(f::Path{GATExpr{:generator}, GATExpr})::GATExpr = compose(getvalue(model), collect(f)...)

  function decompose(f::GATExpr) 
    args = if f isa GATExpr{:generator}
      [f]
    elseif f isa GATExpr{:id}
      GATExpr{:generator}[]
    elseif f isa GATExpr{:compose}
      f.args
    end
    Path(args, dom(f), codom(f)) 
  end
  
  function ob_set()::FinSet
    P = getvalue(model)
    haskey(P.generators, :AttrType) || return FinSet(generators(P, :Ob))
    FinSet(vcat(generators(P, :Ob), generators(P, :AttrType)))
  end

  function gen_set()::FinSet
    P = getvalue(model) 
    haskey(P.generators, :Attr) || return FinSet(generators(P, :Hom))
    FinSet(vcat(generators(P, :Hom), generators(P, :Attr)))
  end
end

# ob_generators(C::FinCatPresentation) = generators(presentation(C), :Ob)
# ob_generators(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}) = let P = presentation(C)
#   vcat(generators(P, :Ob), generators(P, :AttrType))
# end

# hom_generators(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}) = let P = presentation(C)
#   vcat(generators(P, :Hom), generators(P, :Attr))
# end


# ob_generator(C::FinCatPresentation, x) = ob(C, presentation(C)[x])
# ob_generator(C::FinCatPresentation, x::GATExpr{:generator}) = ob(C, x)
# ob_generator_name(C::FinCatPresentation, x::GATExpr{:generator}) = first(x)

# hom_generator(C::FinCatPresentation, f) = hom(C, presentation(C)[f])
# hom_generator(C::FinCatPresentation, f::GATExpr{:generator}) = hom(C, f)
# hom_generator_name(C::FinCatPresentation, f::GATExpr{:generator}) = first(f)

# ob(C::FinCatPresentation, x::GATExpr) =
#   gat_typeof(x) == :Ob ? x : error("Expression $x is not an object")
# ob(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, x::GATExpr) =
#   gat_typeof(x) ∈ (:Ob, :AttrType) ? x :
#     error("Expression $x is not an object or attribute type")

# hom(C::FinCatPresentation, f) = hom_generator(C, f)
# hom(C::FinCatPresentation, fs::AbstractVector) =
#   mapreduce(f -> hom(C, f), compose, fs)
# hom(C::FinCatPresentation, f::GATExpr) =
#   gat_typeof(f) == :Hom ? f : error("Expression $f is not a morphism")
# hom(::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, f::GATExpr) =
#   gat_typeof(f) ∈ (:Hom, :Attr, :AttrType) ? f :
#     error("Expression $f is not a morphism or attribute")

id(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, x::AttrTypeExpr) = x
compose(C::Union{FinCatPresentation{ThSchema.Meta.T},FinCatPresentation{ThPointedSetSchema.Meta.T}}, f::AttrTypeExpr, g::AttrTypeExpr) =
  (f == g) ? f : error("Invalid composite of attribute type identities: $f != $g")


# # Use generator names, rather than generators themselves, for Dict keys. Enforced by FinDomFunctor constructor automatically.
ob_key(C::FinCatPresentation, x) = presentation_key(x)

hom_key(C::FinCatPresentation, f) = presentation_key(f)

presentation_key(name::Union{AbstractString,Symbol}) = name

presentation_key(expr::GATExpr{:generator}) = first(expr)

decompose(C::FinCatPresentation, f::GATExpr{:compose}) = args(f)

function Base.show(io::IO, C::FinCatPresentation)
  print(io, "FinCat(")
  show(io, presentation(C))
  print(io, ")")
end

end # module