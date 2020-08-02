module SInstances
export Schema, SchemaExpr, ConcreteExpr, AttrExpr, FreeSchema,
  SchemaDesc, AbstractSInstance, SInstance,
  TheoryDecGraph, DecGraph

using Catlab.GAT, Catlab.Syntax, Catlab.Present, Catlab.Theories
using StructArrays
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

struct SchemaDesc{Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}
  function SchemaDesc{Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}() where
    {Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}
    new{Ob,Hom,Dom,Codom,Concrete,Attr,AttrDom,AttrCodom}()
  end
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

function tables_type(Ts::Tuple,sd::SchemaDesc)
  cols = [Tuple{Symbol,DataType}[] for ob in sd.ob]
  for i in 1:length(sd.hom)
    push!(cols[sd.dom[i]], (sd.hom[i],Int))
  end
  for i in 1:length(sd.attr)
    push!(cols[sd.attr_dom[i]], (sd.attr[i],Ts[sd.attr_codom[i]]))
  end

  struct_array_types = [StructArray{NamedTuple{Tuple(first.(cols[i])), Tuple{last.(cols[i])...}}}
                        for i in 1:length(sd.ob)]
  NamedTuple{sd.ob,Tuple{struct_array_types...}}
end

abstract type AbstractSInstance{Ts,S} end

struct SInstance{Ts <: Tuple,S <: SchemaDesc,TablesType <: NamedTuple}
  tables::TablesType
  function SInstance{Ts,S}() where {Ts <: Tuple, S <: SchemaDesc}
    sd = S()
    tt = tables_type(Tuple(Ts.parameters),sd)
    empty_tables = [tt.parameters[2].parameters[i](undef,0) for i in 1:length(sd.ob)]
    new{Ts,S,tt}(tt(empty_tables))
  end
end

@present TheoryDecGraph(FreeSchema) begin
  V::Ob
  E::Ob
  X::Concrete

  src::Hom(E,V)
  tgt::Hom(E,V)
  vdec::Attr(V,X)
  edec::Attr(E,X)
end

const DecGraph{T} = SInstance{Tuple{T},typeof(SchemaDesc(TheoryDecGraph))}

end
