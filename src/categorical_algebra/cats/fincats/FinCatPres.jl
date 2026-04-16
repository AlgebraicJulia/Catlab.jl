""" Symbolic categories """
module FinCatPres 
export FinCatPresentation, ThFinCat, presentation

using StructEquality

using GATlab, ACSets
import GATlab: equations, getvalue

using ......Theories: ThSchema, ThPointedSetSchema, AttrTypeExpr, FreeSchema, FreePointedSetSchema
import ......Theories: id, compose, dom, codom
                      
using ......BasicSets: FinSet, SetOb
using ...Paths: Path, src, tgt
using ..FinCats: ThFinCat
import ..FinCats: FinCat, decompose


const Ob = Union{FreeSchema.Ob{:generator}, FreeSchema.AttrType{:generator}}
const Hom = Union{FreeSchema.Hom, FreeSchema.Attr}
const Gen = Union{FreeSchema.Attr{:generator}, FreeSchema.Hom{:generator}}

const PointedOb = Union{FreePointedSetSchema.Ob{:generator}, FreePointedSetSchema.AttrType{:generator}}
const PointedHom = Union{FreePointedSetSchema.Hom, FreePointedSetSchema.Attr, FreePointedSetSchema.AttrType}
const PointedGen = Union{FreePointedSetSchema.Attr{:generator}, FreePointedSetSchema.Hom{:generator}}

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
  FinCatPresentation{ThPointedSetSchema.Meta.T}(pres)
end

# Other methods
#-------------

function decompose(::FinCatPresentation, f::Union{FreeSchema.Attr{:generator},FreeSchema.Hom{:generator}}) 
  Path([f], f.type_args...)
end

function decompose(::FinCatPresentation,
                   f::Union{FreePointedSetSchema.Attr{:generator},
                            FreePointedSetSchema.Hom{:generator}})
  Path([f], f.type_args...)
end

decompose(::FinCatPresentation, f::FreeSchema.Hom{:id}) = let x = only(f.args);
  Path([], x, x)
end

decompose(::FinCatPresentation, f::FreePointedSetSchema.Hom{:id}) =
  let x = only(f.args);
    Path([], x, x)
  end

function decompose(C::FinCatPresentation, f::Union{FreeSchema.Attr{:compose},FreeSchema.Hom{:compose}}) 
  S = Schema(getvalue(C))
  Path(f.args, dom(S, nameof(first(f.args))), codom(S, nameof(last(f.args))))
end

function decompose(C::FinCatPresentation,
                   f::Union{FreePointedSetSchema.Attr{:compose},
                            FreePointedSetSchema.Hom{:compose}})
  S = Schema(getvalue(C))
  Path(f.args, dom(S, nameof(first(f.args))), codom(S, nameof(last(f.args))))
end


equations(C::FinCatPresentation) = equations(presentation(C))

presentation(C::FinCatPresentation) = C.presentation # synonym for getvalue

# Implementation of FinCat interface
####################################
# AnyHom = Union{FreeSchema.Hom{:generator}, FreeSchema.Hom{:compose}, FreeSchema.Hom{:id}}

@instance ThFinCat{Ob, Hom, Gen} [model::FinCatPresentation{ThSchema.Meta.T}] begin
  src(f::Gen)::Ob = first(f.type_args)

  tgt(f::Gen)::Ob = last(f.type_args)

  dom(f::Hom)::Ob = dom(f)

  codom(f::Hom)::Ob = codom(f)
  
  id(x::Ob)::Hom = if x isa FreeSchema.AttrType{:generator}
    FreeSchema.Hom{:id}([x], [x, x])
  else
    id(x)
  end

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

@instance ThFinCat{PointedOb, PointedHom, PointedGen} [model::FinCatPresentation{ThPointedSetSchema.Meta.T}] begin
  src(f::PointedGen)::PointedOb = first(f.type_args)

  tgt(f::PointedGen)::PointedOb = last(f.type_args)

  dom(f::PointedHom)::PointedOb =
    f isa FreePointedSetSchema.AttrType ? f : first(f.type_args)

  codom(f::PointedHom)::PointedOb =
    f isa FreePointedSetSchema.AttrType ? f : last(f.type_args)

  id(x::PointedOb)::PointedHom = id(x)

  compose(f::PointedHom, g::PointedHom)::PointedHom = compose(f, g)

  to_hom(g::PointedGen)::PointedHom = g

  function ob_set()::SetOb
    P = getvalue(model)
    v = PointedOb[generators(P, :Ob);
                  haskey(P.generators, :AttrType) ? generators(P, :AttrType) : []]
    SetOb(getvalue(FinSet(v)))
  end

  function gen_set()::FinSet
    P = getvalue(model)
    haskey(P.generators, :Attr) || return FinSet(generators(P, :Hom))
    v = PointedGen[generators(P, :Hom); generators(P, :Attr)]
    FinSet(v)
  end

  hom_set()::SetOb = SetOb(PointedHom)

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
