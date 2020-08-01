using Catlab.GAT, Catlab.Syntax, Catlab.Present, Catlab.Theories
using LabelledArrays
using Match

@theory Category(Ob,Hom) => Schema(Ob,Hom,Concrete,Attr) begin
  Concrete::TYPE
  Attr(dom::Ob,codom::Concrete)::TYPE

  precompose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::Concrete)
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type ConcreteExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@syntax FreeSchema(ObExpr,HomExpr,ConcreteExpr,AttrExpr) Schema begin
  # should have a normal representation for precompose of a morphism + a generator attribute
end

@present TheoryDecGraph(FreeSchema) begin
  V::Ob
  E::Ob
  X::Concrete

  src::Hom(E,V)
  tgt::Hom(E,V)
  dec::Attr(V,X)
end

struct SchemaDesc{Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}
  function SchemaDesc(pres::Presentation{Schema})
    obs, homs, concretes, attrs = generators(pres, :Ob), generators(pres,:Hom),
      generators(pres,:Concrete), generators(pres,:Attr)
    ob_syms, hom_syms, concrete_syms, attr_syms = nameof.(obs), nameof.(homs),
      nameof.(concretes), nameof.(attrs)
    ob_num = ob -> findfirst(ob_syms .== ob)::Int
    concrete_num = c -> findfirst(concrete_syms .== c)::Int
    new{Tuple(ob_syms), Tuple(hom_syms),
        Tuple(@. ob_num(nameof(dom(homs)))), Tuple(@. ob_num(nameof(codom(homs)))),
        Tuple(concrete_syms), Tuple(attr_syms),
        Tuple(@. ob_num(nameof(dom(attrs)))), Tuple(@. concrete_num(nameof(codom(attrs))))}()
  end
end

function Base.getproperty(S::SchemaDesc{Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom},i::Symbol
                  ) where {Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}
  @match i begin
    :ob => Ob
    :hom => Hom
    :dom => Dom
    :codom => Codom
    :concrete => Concrete
    :attr => Attr
    :attr_dom => AttrDom
    :attr_codom => AttrCodom
    _ => error("unsupported index on SchemaDesc")
  end
end

struct NamedColumns{L,Ts,D<:NamedTuple{L}}
  __x::D
  NamedColumns(;args...) = begin
    __x = (;args...)
    L = keys(__x)
    Ts = Tuple{[eltype(__x[l]) for l in L]...}
    new{L,Ts,typeof(__x)}(__x)
  end
end

function Base.getproperty(nc::NamedColumns, name::Symbol)
  _getproperty(nc,Val(name))
end

@generated function _getproperty(nc::NamedColumns{L}, ::Val{name}) where {L,name}
  if name ∈ L
    :(nc.__x.$name)
  else
    throw(KeyError(name))
  end
end

struct AttrStorage{Attrs, AttrCodoms, CodomTypes, AttrTypes}
  __nc::NamedColumns{Attrs,AttrTypes}
  AttrStorage{Attrs,AttrCodoms,CodomTypes}(
    attrs::NamedColumns{Attrs,AttrTypes}) where {Attrs,AttrCodoms,CodomTypes,AttrTypes} = begin
      for i in 1:length(Attrs)
        @assert(AttrTypes.parameters[i] == CodomTypes.parameters[AttrCodoms[i]])
      end
      new{Attrs,AttrCodoms,CodomTypes,AttrTypes}(attrs)
  end
end

function Base.getproperty(attrs::AttrStorage, name::Symbol)
  _getproperty(attrs,Val(name))
end

@generated function _getproperty(attrs::AttrStorage{Attrs}, ::Val{name}) where {Attrs,name}
  if name ∈ L
    :(attrs.__nc.$name)
  else
    throw(KeyError(name))
  end
end

const NamedSVector{Names,T,N} = SLArray{Tuple{N},T,1,N,Names}

abstract type AbstractSInstance{Ts,S} end

mutable struct SInstance{Ts,S,Ob,Hom,Attr,AttrCodom} <: AbstractSInstance{Ts,S}
  nparts::NamedSVector{Ob,Int}
  subparts::NamedSVector{Hom,Vector{Int}}
  attrs::AttrStorage{Attr,AttrCodom,Ts}
end

function SInstanceTypeParams(pres::Presentation{Schema})
  S = SchemaDesc(pres)
  (S,S.ob,S.hom,S.attr,S.codom)
end

const AbstractDecGraph{T} = AbstractSInstance{Tuple{T},SchemaDesc(TheoryDecGraph)}

const DecGraph{T} = SInstance{Tuple{T},SInstanceTypeParams(TheoryDecGraph)...}

nparts(inst::SInstance, type::Symbol) = inst.nparts[type]

has_part(inst::SInstance, type::Symbol) = _has_part(inst,Val(type))

@generated _has_part(inst::SInstance{Ts,S}, ::Val{type}) where {Ts,S,type} =
  type ∈ S.ob

has_part(inst::SInstance, type::Symbol, part::Int) = 1 <= part <= nparts(cset, type)

subpart(inst::SInstance, part, name::Symbol) = subpart(inst, name)[part]
subpart(inst::SInstance, name::Symbol) = _subpart(inst, Val(name))

@generated function _subpart(cset::SInstance{Ts,S}, ::Val{name}) where {S,Ts,name}
  if name ∈ S.hom
    :(csets.subparts.$name)
  elseif name ∈ S.attr
    :(csets.attrs.$name)
  else
    throw(KeyError(name))
  end
end
