export Schema, FreeSchema, Data, Attr, SchemaExpr, DataExpr, AttrExpr,
  FinProductSchema, FreeFinProductSchema, ob, proj1, proj2,
  FinLimitSchema, FreeFinLimitSchema, incl, left, right

using MLStyle: @match
using ...Present

import ...Present: Presentation

# Schema
########

""" Theory of a *schema* for attributed C-sets.

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
  # TODO: We should have a normal form for the composition of a morphism with a
  # data attribute.
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

""" Theory of a *schema with finite products*

Recall that a *finite product sketch* is a (directed) graph equipped with a set
of equations and a set of cones over finite, discrete diagrams. The sketch
presents an algebraic structure whose operations may involve finite products.

A *finite product schema*, as defined here, is the same as a finite product
sketch, except that data attributes are allowed. Limit cones are specified in a
biased style via terminal objects and binary products. Products of attribute
types are not supported because, by the universal property of the product, an
attribute into a product type can always be replaced by several attributes into
the basic types.

We use sketches as a minimalistic syntax for specifying limits in C-sets. Note
that the models of this GAT are *not* models of sketches. For GATs whose models
are actually categories with finite products, see [`CartesianCategory`](@ref)
and [`CategoryWithProducts`](@ref).
"""
@theory FinProductSchema{Ob,Hom,Data,Attr,Terminal,Product} <:
    Schema{Ob,Hom,Data,Attr} begin
  Terminal(ob::Ob)::TYPE
  Product(ob::Ob, proj1::Hom(ob,A), proj2::Hom(ob,B))::TYPE ⊣ (A::Ob, B::Ob)
end

@syntax FreeFinProductSchema{ObExpr,HomExpr,DataExpr,AttrExpr,
                             GATExpr,GATExpr} FinProductSchema begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g; strict=true), id)
  compose(f::Hom, x::Attr) = associate_unit(new(f,x; strict=true), id)
end

""" Theory of a *schema with finite limits*

Recall that a *finite limit sketch* is a (directed) graph equipped with a set of
equations and a set of cones over finite diagrams. The sketch presents an
algebraic structure whose operations may involve finite limits.

A *finite limit schema* is the same as a finite limit sketch except that data
attributes are allowed. Limit cones are specified in a biased style via terminal
objects and binary products, equalizers, and pullbacks.
"""
@theory FinLimitSchema{Ob,Hom,Data,Attr,Terminal,Product,Equalizer,Pullback} <:
    FinProductSchema{Ob,Hom,Data,Attr,Terminal,Product} begin
  Equalizer(ob::Ob, incl::Hom(ob,A),
            left::Hom(A,B), right::Hom(A,B))::TYPE ⊣ (A::Ob, B::Ob)
  Pullback(ob::Ob, proj1::Hom(ob,A), proj2::Hom(ob,B),
           left::Hom(A,C), right::Hom(B,C))::TYPE ⊣ (A::Ob, B::Ob, C::Ob)
  # FIXME: If overloadingg type constructors were allowed, we could just use
  # `Pullback` again instead of `PullbackAttr`.
  #PullbackAttr(ob::Ob, proj1::Hom(ob,A), proj2::Hom(ob,B),
  #             left::Attr(A,X), right::Attr(B,X))::TYPE ⊣ (A::Ob, B::Ob, X::Data)
end

@syntax FreeFinLimitSchema{ObExpr,HomExpr,DataExpr,AttrExpr,
                           GATExpr,GATExpr,GATExpr,GATExpr} FinLimitSchema begin
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
