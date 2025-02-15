""" Symbolic categories """
module FinCatPres 
export FinCatPresentation, ThFinCat, presentation

using StructEquality

using GATlab, ACSets
import GATlab: equations, getvalue

using ......Theories: ThSchema, ThPointedSetSchema, AttrTypeExpr, FreeSchema
import ......Theories: id, compose, dom, codom
                      
using ......BasicSets: FinSet
using ...Paths: Path, src, tgt
using ..FinCats: ThFinCat
import ..FinCats: FinCat


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

equations(C::FinCatPresentation) = equations(presentation(C))

presentation(C::FinCatPresentation) = C.presentation # synonym for getvalue

# Implementation of FinCat interface
####################################
# AnyHom = Union{FreeSchema.Hom{:generator}, FreeSchema.Hom{:compose}, FreeSchema.Hom{:id}}

@instance ThFinCat{Ob, Hom, Gen, Path{<:Ob, <:Gen}
                  } [model::FinCatPresentation{T}] where {T} begin
  src(f::Gen)::Ob = dom(f)

  tgt(f::Gen)::Ob = codom(f)

  dom(f::Hom)::Ob = dom(f)

  codom(f::Hom)::Ob = codom(f)
  
  id(x::Ob)::Hom = id(x)

  function compose(f::Path{<:Ob, <:Gen})::Hom 
    length(f) == 0 && return id(src(f))
    length(f) == 1 && return only(f)
    compose(collect(f)...)
  end

  function decompose(f::Hom)::Path{<:Ob, <:Gen}
    args = if f isa Gen
      Gen[f]
    elseif f isa GATExpr{:id}
      Gen[]
    elseif f isa GATExpr{:compose}
      f.args
    end
    Path(Vector{Gen}(args), dom(f), codom(f))  #{Ob,Gen,Vector{Gen}} 
  end
  
  function ob_set()::FinSet
    P = getvalue(model)
    v = Ob[generators(P, :Ob); 
           haskey(P.generators, :AttrType) ? generators(P, :AttrType) : []]
    FinSet(v)
  end

  function gen_set()::FinSet
    P = getvalue(model) 
    haskey(P.generators, :Attr) || return FinSet(generators(P, :Hom))
    v = Gen[generators(P, :Hom); generators(P, :Attr)]
    FinSet(v)
  end
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

decompose(::FinCatPresentation, f::GATExpr{:compose}) = args(f)

function Base.show(io::IO, C::FinCatPresentation)
  print(io, "FinCat(")
  show(io, presentation(C))
  print(io, ")")
end

end # module
