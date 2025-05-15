""" Symbolic categories """
module FinCatPres 
export FinCatPresentation, ThFinCat, presentation

using StructEquality

using GATlab, ACSets
import GATlab: equations, getvalue

using ......Theories: ThSchema, ThPointedSetSchema, AttrTypeExpr, FreeSchema
import ......Theories: id, compose, dom, codom
                      
using ......BasicSets: FinSet, SetOb
using ...Paths: Path, src, tgt
using ..FinCats: ThFinCat
import ..FinCats: FinCat, decompose


const Ob = Union{FreeSchema.Ob{:generator},FreeSchema.AttrType{:generator}}
const Hom = Union{FreeSchema.Hom,FreeSchema.Attr}
const Gen = Union{FreeSchema.Attr{:generator},FreeSchema.Hom{:generator}}

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

function decompose(::FinCatPresentation, f::Union{FreeSchema.Attr{:generator},FreeSchema.Hom{:generator}}) 
  Path([f], f.type_args...)
end

decompose(::FinCatPresentation, f::FreeSchema.Hom{:id}) = let x = only(f.args);
  Path([], x, x)
end

function decompose(C::FinCatPresentation, f::Union{FreeSchema.Attr{:compose},FreeSchema.Hom{:compose}}) 
  S = Schema(getvalue(C))
  Path(f.args, dom(S, nameof(first(f.args))), codom(S, nameof(last(f.args))))
end


equations(C::FinCatPresentation) = equations(presentation(C))

presentation(C::FinCatPresentation) = C.presentation # synonym for getvalue

# Implementation of FinCat interface
####################################
# AnyHom = Union{FreeSchema.Hom{:generator}, FreeSchema.Hom{:compose}, FreeSchema.Hom{:id}}

@instance ThFinCat{Ob, Hom, Gen} [model::FinCatPresentation{T}] where {T} begin
  src(f::Gen)::Ob = dom(f)

  tgt(f::Gen)::Ob = codom(f)

  dom(f::Hom)::Ob = dom(f)

  codom(f::Hom)::Ob = codom(f)
  
  id(x::Ob)::Hom = id(x)

  compose(f::Hom, g::Hom)::Hom = compose(f, g)

  to_hom(g::Gen)::Hom = g
  
  function ob_set()::SetOb
    P = getvalue(model)
    v = Ob[generators(P, :Ob); 
           haskey(P.generators, :AttrType) ? generators(P, :AttrType) : []]
    SetOb(getvalue(FinSet(v)))
  end

  function gen_set()::FinSet
    P = getvalue(model) 
    haskey(P.generators, :Attr) || return FinSet(generators(P, :Hom))
    v = Gen[generators(P, :Hom); generators(P, :Attr)]
    FinSet(v)
  end

  hom_set()::SetOb = SetOb(Hom)

end

id(::Union{FinCatPresentation{ThSchema.Meta.T},
           FinCatPresentation{ThPointedSetSchema.Meta.T}
           }, 
   x::AttrTypeExpr) = x

compose(::Union{FinCatPresentation{ThSchema.Meta.T},
                FinCatPresentation{ThPointedSetSchema.Meta.T}}, 
        f::AttrTypeExpr, g::AttrTypeExpr) =
  (f == g) ? f : error("Invalid composite of attribute type identities: $f != $g")


# Use generator names, rather than generators themselves, for Dict keys. 
# Enforced by FinDomFunctor constructor automatically.
ob_key(::FinCatPresentation, x) = presentation_key(x)

hom_key(::FinCatPresentation, f) = presentation_key(f)

presentation_key(name::Union{AbstractString,Symbol}) = name

presentation_key(expr::GATExpr{:generator}) = first(expr)

function Base.show(io::IO, C::FinCatPresentation)
  print(io, "FinCat(")
  show(io, presentation(C))
  print(io, ")")
end

end # module
