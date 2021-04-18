export Schema, FreeSchema, Data, Attr, SchemaExpr, DataExpr, AttrExpr

using MLStyle: @match
using ...Present

import ...Present: Presentation

# Schema
########

""" The GAT that parameterizes Attributed C-sets

A schema is comprised of a category C, a discrete category D, and a profunctor
Attr : C^op x D → Set. In GAT form, this is given by extending the theory of
categories with two extra types, Data for objects of D, and Attr, for elements
of the sets given by the profunctor.
"""
@theory Schema{Ob,Hom,Data,Attr} <: Category{Ob,Hom} begin
  Data::TYPE
  Attr(dom::Ob,codom::Data)::TYPE

  """ Composition is given by the action of the profunctor on C.
  """
  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::Data)

  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Data, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::Data, a::Attr(A,X))
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type DataExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@syntax FreeSchema{ObExpr,HomExpr,DataExpr,AttrExpr} Schema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

# Type-level representation of Schema
#####################################

""" CatDesc is a type-level description of a category

In order to have Attributed C-sets that are parameterized by schemas, we have to
use the type of this struct as the type parameter to get around Julia's
restrictions on what sort of thing can appear as a type parameter.

We split a Schema up into two types: CatDesc (describing the category) and
AttrDesc (describing the discrete category and the profunctor). This allows us
to have C-sets as Attributed C-sets with an empty AttrDesc.
"""
struct CatDesc{Ob,Hom,Dom,Codom}
  function CatDesc{Ob,Hom,Dom,Codom}() where {Ob,Hom,Dom,Codom}
    new{Ob,Hom,Dom,Codom}()
  end
  function CatDesc(pres::Presentation{Schema})
    obs, homs = generators(pres, :Ob), generators(pres,:Hom)
    ob_syms, hom_syms = nameof.(obs), nameof.(homs)
    ob_num = ob -> findfirst(ob_syms .== ob)::Int
    new{Tuple(ob_syms), Tuple(hom_syms),
        Tuple(@. ob_num(nameof(dom(homs)))), Tuple(@. ob_num(nameof(codom(homs))))}()
  end
end

CatDescType(pres::Presentation{Schema}) = typeof(CatDesc(pres))

ob(::Type{T}) where {Ob,T <: CatDesc{Ob}} = Ob
hom(::Type{T}) where {Ob,Hom, T <: CatDesc{Ob,Hom}} = Hom
dom(::Type{T}) where {Ob,Hom,Dom, T <: CatDesc{Ob,Hom,Dom}} = Dom
codom(::Type{T}) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}} = Codom

function ob_num(CD::Type{T}, ob::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Ob .== ob)::Int
end

function hom_num(CD::Type{T}, hom::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Hom .== hom)::Int
end

function dom_num(CD::Type{T}, hom::Int) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Dom[hom]
end

function dom_num(CD::Type{<:CatDesc}, hom::Symbol)
  dom_num(CD, hom_num(CD,hom))
end

function codom_num(CD::Type{T}, hom::Int) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Codom[hom]
end

function codom_num(CD::Type{<:CatDesc}, hom::Symbol)
  codom_num(CD, hom_num(CD,hom))
end

function dom(CD::Type{T}, hom::Union{Int,Symbol}) where
    {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[dom_num(CD,hom)]
end

function codom(CD::Type{T}, hom::Union{Int,Symbol}) where
    {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[codom_num(CD,hom)]
end

""" AttrDesc is a type-level representation of attributes added
to a category to form a schema
"""
struct AttrDesc{CD,Data,Attr,ADom,ACodom}
  function AttrDesc{CD,Data,Attr,ADom,ACodom}() where {CD,Data,Attr,ADom,ACodom}
    new{CD,Data,Attr,ADom,ACodom}()
  end
  function AttrDesc(pres::Presentation{Schema})
    CD = CatDescType(pres)
    datas, attrs = generators(pres, :Data), generators(pres,:Attr)
    data_syms, attr_syms = nameof.(datas), nameof.(attrs)
    ob_num = ob -> findfirst(Theories.ob(CD) .== ob)::Int
    data_num = ob -> findfirst(data_syms .== ob)::Int
    new{CD,Tuple(data_syms), Tuple(attr_syms),
        Tuple(@. ob_num(nameof(dom(attrs)))), Tuple(@. data_num(nameof(codom(attrs))))}()
  end
  function AttrDesc(::CatDesc{Ob,Hom,Dom,Codom}) where {Ob,Hom,Dom,Codom}
    new{CatDesc{Ob,Hom,Dom,Codom},(),(),(),()}
  end
end

AttrDescType(pres::Presentation{Schema}) = typeof(AttrDesc(pres))

data(::Type{T}) where {CD,Data, T <: AttrDesc{CD,Data}} = Data
attr(::Type{T}) where {CD,Data,Attr, T <: AttrDesc{CD,Data,Attr}} = Attr
adom(::Type{T}) where {CD,Data,Attr,ADom,
                       T <: AttrDesc{CD,Data,Attr,ADom}} = ADom
acodom(::Type{T}) where {CD,Data,Attr,ADom,ACodom,
                         T <: AttrDesc{CD,Data,Attr,ADom,ACodom}} = ACodom

function data_num(AD::Type{T}, data::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  findfirst(Data .== data)::Int
end

function attr_num(AD::Type{T}, attr::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  findfirst(Attr .== attr)::Int
end

function dom_num(AD::Type{T}, attr::Int) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  ADom[attr]
end

function dom_num(AD::Type{<:AttrDesc}, attr::Symbol)
  dom_num(AD,attr_num(AD,attr))
end

function codom_num(AD::Type{T}, attr::Int) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  ACodom[attr]
end

function codom_num(AD::Type{<:AttrDesc}, attr::Symbol)
  codom_num(AD,attr_num(AD,attr))
end

function dom(AD::Type{T}, attr::Union{Int,Symbol}) where
    {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  ob(CD)[dom_num(AD,attr)]
end

function codom(AD::Type{T}, attr::Union{Int,Symbol}) where
    {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  Data[codom_num(AD,attr)]
end

function attrs_by_codom(AD::Type{T}) where
    {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  abc = Dict{Symbol,Array{Symbol}}()
  for i in eachindex(Attr)
    a = Attr[i]
    d = Data[ACodom[i]]
    if d ∈ keys(abc)
      push!(abc[d],a)
    else
      abc[d] = [a]
    end
  end
  abc
end

SchemaType(pres::Presentation{Schema}) = (CatDescType(pres),AttrDescType(pres))

"""
Inverse of SchemaType. Converts a CatDesc and AttrDesc into a Presentation. 
"""
function Presentation(CD::Type{T}, AD::Type{S}) where {T <: CatDesc, S <: AttrDesc}
  pres = Presentation(FreeSchema)

  obs = map(x -> Ob(FreeSchema, x), collect(ob(CD)))
  homs = map(Hom, collect(hom(CD)), obs[collect(dom(CD))], obs[collect(codom(CD))])
  datas = map(x -> Data(FreeSchema.Data, x), collect(data(AD)))
  attrs = map(FreeSchema.Attr, collect(attr(AD)), obs[collect(adom(AD))], datas[collect(acodom(AD))])

  map(gens -> add_generators!(pres, gens), [obs, homs, datas, attrs])
  return pres
end