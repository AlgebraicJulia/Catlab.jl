module SInstances
export Schema, SchemaExpr, ConcreteExpr, AttrExpr, FreeSchema,
  SchemaDesc, AbstractSInstance, SInstance,
  nparts, add_part!, add_parts!, _add_parts!, subpart, incident,
  TheoryGraph, AbstractGraph, Graph,
  TheoryDecGraph, AbstractDecGraph, DecGraph

using Catlab.GAT, Catlab.Syntax, Catlab.Present, Catlab.Theories
using StructArrays
using MLStyle

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

struct CatDesc{Ob,Hom,Dom,Codom}
  function CatDesc{Ob,Hom,Dom,Codom}() where
    {Ob,Hom,Dom,Codom}
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

function Base.getproperty(S::Type{T},i::Symbol) where
  {Ob,Hom,Dom,Codom,T<:CatDesc{Ob,Hom,Dom,Codom}}
  @match i begin
    :ob => Ob
    :hom => Hom
    :dom => Dom
    :codom => Codom
    _ => error("unsupported index $i on CatDesc")
  end
end

struct AttrDesc{CD,Concrete,Attr,ADom,ACodom}
  function AttrDesc{CD,Concrete,Attr,ADom,ACodom}() where {CD,Concrete,Attr,ADom,ACodom}
    new{CD,Concrete,Attr,ADom,ACodom}()
  end
  function AttrDesc(pres::Presentation{Schema})
    CD = CatDescType(pres)
    concretes, attrs = generators(pres, :Concrete), generators(pres,:Attr)
    concrete_syms, attr_syms = nameof.(concretes), nameof.(attrs)
    ob_num = ob -> findfirst(CD.ob .== ob)::Int
    concrete_num = ob -> findfirst(concrete_syms .== ob)::Int
    new{CD,Tuple(concrete_syms), Tuple(attr_syms),
        Tuple(@. ob_num(nameof(dom(attrs)))), Tuple(@. concrete_num(nameof(codom(attrs))))}()
  end
  function AttrDesc(::CatDesc{Ob,Hom,Dom,Codom}) where {Ob,Hom,Dom,Codom}
    new{CatDesc{Ob,Hom,Dom,Codom},(),(),(),()}
  end
end

AttrDescType(pres::Presentation{Schema}) = typeof(AttrDesc(pres))

function Base.getproperty(S::Type{T}, i::Symbol) where
  {CD,Concrete,Attr,ADom,ACodom,T <: AttrDesc{CD,Concrete,Attr,ADom,ACodom}}
  @match i begin
    :cd => CD
    :concrete => Concrete
    :attr => Attr
    :adom => ADom
    :acodom => ACodom
    _ => error("unsupported index $i on AttrDesc")
  end
end

function make_index(CD::Type{<:CatDesc},AD::Type{<:AttrDesc},Ts::Type{<:Tuple},Idxed::Tuple)
    attr_num = attr -> findfirst(AD.attr .== attr)::Int
    function make_idx(name)
      if name ∈ CD.hom
        Vector{Vector{Int}}()
      elseif name ∈ AD.attr
        Dict{Ts.parameters[AD.acodom[attr_num(name)]],Vector{Int}}()
      else
        error("invalid index parameter")
      end
    end
  NamedTuple{Idxed}(Tuple(make_idx(name) for name in Idxed))
end

function table_desc(::Type{CatDesc{Ob,Hom,Dom,Codom}},
                    ::Type{AttrDesc{CatDesc{Ob,Hom,Dom,Codom},Concrete,Attr,ADom,ACodom}},
                    ts::Tuple) where {Ob,Hom,Dom,Codom,Concrete,Attr,ADom,ACodom}
  cols = [Tuple{Symbol,DataType}[] for ob in Ob]
  for i in 1:length(Hom)
    push!(cols[Dom[i]], (Hom[i],Int))
  end
  for i in 1:length(Attr)
    push!(cols[ADom[i]], (Attr[i],ts[ACodom[i]]))
  end
  [(col_names = first.(cols[i]), col_types = last.(cols[i])) for i in 1:length(Ob)]
end

abstract type AbstractSInstance{CD,AD,Ts} end

struct SInstance{CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed,
                 TablesType <: NamedTuple, IndexType <: NamedTuple} <: AbstractSInstance{CD,AD,Ts}
  tables::TablesType
  index::IndexType
  function SInstance{CD}() where {CD <: CatDesc}
    SInstance{CD,typeof(AttrDesc(CD())),Tuple{}}()
  end
  function SInstance{CD,AD,Ts,Idxed}() where {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed}
    td = table_desc(CD,AD,Tuple(Ts.parameters))
    empty_tables = NamedTuple{CD.ob}(
      [StructArray{NamedTuple{Tuple(td[i].col_names), Tuple{td[i].col_types...}}}(undef,0)
       for i in 1:length(CD.ob)])
    index = make_index(CD,AD,Ts,Idxed)
    new{CD,AD,Ts,Idxed,typeof(empty_tables),typeof(index)}(empty_tables,index)
  end
  function SInstance{CD,AD,Ts,Idxed,TT,IT}() where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    SInstance{CD,AD,Ts,Idxed}()
  end
  function SInstance{CD,AD,Ts,Idxed,TT,IT}(tables::TT,index::IT) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    new{CD,AD,Ts,Idxed,TT,IT}(tables,index)
  end
end


function fields(::Type{T}) where {T <: NamedTuple}
  T.parameters[1]
end

function fieldtype(::Type{T},i::Integer) where {T <: NamedTuple}
  fieldtypes(T)[i]
end

function fieldtype(::Type{T},s::Symbol) where {T <: NamedTuple}
  i = findfirst(fields(T) .== s)
  fieldtype(T,i)
end

function fields(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fields(T.parameters[1])
end

function Base.fieldtypes(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fieldtypes(T.parameters[1])
end

function fieldtype(::Type{T},i::Integer) where {T <: StructArray{<:NamedTuple}}
  fieldtype(T.parameters[1],i)
end

function fieldtype(::Type{T},s::Symbol) where {T <: StructArray{<:NamedTuple}}
  fieldtype(T.parameters[1],s)
end

function Base.:(==)(x1::T, x2::T) where T <: SInstance
  x1.tables == x2.tables
end

function Base.copy(ins::T) where T <: SInstance
  T(copy(ins.tables),copy(ins.index))
end

Base.empty(ins::T) where T <: SInstance = T()

function Base.show(io::IO, mime::MIME"text/plain", ins::AbstractSInstance{CD,AD,Ts}) where {CD,AD,Ts}
  println(io,"SInstance")
  for ob in CD.ob
    println(io, "  $ob = 1:$(nparts(ins,ob))")
  end
  for (i,hom) in enumerate(CD.hom)
    println(io, "  $hom : $(CD.ob[CD.dom[i]]) → $(CD.ob[CD.codom[i]])")
    println(io, "    $(subpart(ins,hom))")
  end
  for (i,conc) in enumerate(AD.concrete)
    println(io, "  $conc = $(Ts.parameters[i])")
  end
  for (i,attr) in enumerate(AD.attr)
    println(io, "  $attr : $(CD.ob[AD.adom[i]]) ⇒ $(AD.concrete[AD.acodom[i]])")
    println(io, "    $(subpart(ins,attr))")
  end
end

nparts(ins::SInstance,type::Symbol) = length(ins.tables[type])

haspart(ins::SInstance,type::Symbol,part::Int) = 1 <= part <= nparts(ins,type)

add_part!(ins::SInstance,type::Symbol,subparts::NamedTuple) =
  _add_parts!(ins,Val(type),StructArray([subparts]))[1]
add_parts!(ins::SInstance,type::Symbol,subpartses::StructArray{<:NamedTuple}) =
  _add_parts!(ins,Val(type),subpartses)

@generated function _add_parts!(ins::SInstance{CD,AD,Ts,Idxed,TT},::Val{ob},
                                subpartses::T) where
  {CD,AD,Ts,Idxed,TT,ob,T<:StructArray{<:NamedTuple}}
  @assert T == fieldtype(TT,ob)
  code = quote
    append!(ins.tables.$ob,subpartses)
  end
  for (i,hom) in enumerate(CD.hom)
    if hom ∈ Idxed && CD.ob[CD.codom[i]] == ob
      push!(code.args, :(append!(ins.index.$(hom), repeat([[]],length(subpartses)))))
    end
  end
  inner_loop = Expr(:block)
  for hom in T.parameters[1].parameters[1]
    if hom ∈ Idxed
      if hom ∈ CD.hom
        hom_num = findfirst(CD.hom .== hom)
        index_code = quote
          @assert haspart(ins, $(Expr(:quote, CD.ob[CD.codom[hom_num]])), subparts.$hom)
          push!(ins.index.$(hom)[subparts.$hom],i)
        end
        push!(inner_loop.args, index_code)
      elseif hom ∈ AD.attr
        attr_num = findfirst(CD.attr .== hom)
        index_code = quote
          if subparts.$hom ∈ keys(ins.index.$hom)
            push!(ins.index.$(hom)[subparts.$hom],i)
          else
            ins.index.$(hom)[subparts.$hom] = [i]
          end
        end
        push!(inner_loop.args, index_code)
      end
    end
  end
  quote
    k = length(subpartses)
    n = nparts(ins,ob)
    $code
    for (i,subparts) in enumerate(subpartses)
      $inner_loop
    end
    (n+1):(n+k)
  end
end

subpart(ins::SInstance, part, name::Symbol) = subpart(ins,name)[part]
subpart(ins::SInstance, name::Symbol) = _subpart(ins,Val(name))

@generated function _subpart(ins::SInstance{CD,AD,Ts},::Val{name}) where {CD,AD,Ts,name}
  if name ∈ CD.hom
    i = findfirst(CD.hom .== name)
    dom = CD.ob[CD.dom[i]]
    :(ins.tables.$dom.$name)
  elseif name ∈ AD.attr
    i = findfirst(AD.attr .== name)
    dom = CD.ob[AD.adom[i]]
    :(ins.tables.$dom.$name)
  else
    throw(KeyError(name))
  end
end

incident(ins::SInstance, part, name::Symbol) = _incident(ins, part, Val(name))

get_data_index(d::AbstractDict{K,Int}, k::K) where K =
  get(d, k, nothing)
get_data_index(d::AbstractDict{K,<:AbstractVector{Int}}, k::K) where K =
  get(d, k, 1:0)

@generated function _incident(ins::SInstance{CD,AD,Ts,Idxed}, part, ::Val{name}) where {CD,AD,Ts,Idxed,name}
  if name ∈ Idxed
    if name ∈ CD.hom
      :(ins.index.$name[part])
    else
      :(get_data_index.(Ref(ins.index.$name),part))
    end
  else
    throw(KeyError(name))
  end
end

@present TheoryGraph(FreeSchema) begin
  V::Ob
  E::Ob

  src::Hom(E,V)
  tgt::Hom(E,V)
end

const AbstractGraph = AbstractSInstance{typeof(CatDesc(TheoryGraph))}

const Graph = SInstance{typeof(CatDesc(TheoryGraph)),
                        typeof(AttrDesc(TheoryGraph)),Tuple{},(:src,:tgt)}

@present TheoryDecGraph <: TheoryGraph begin
  X::Concrete

  vdec::Attr(V,X)
  edec::Attr(E,X)
end

const AbstractDecGraph{T} = AbstractSInstance{typeof(CatDesc(TheoryDecGraph)),
                                              typeof(AttrDesc(TheoryDecGraph)),Tuple{T}}

const DecGraph{T} = SInstance{typeof(CatDesc(TheoryDecGraph)),
                              typeof(AttrDesc(TheoryDecGraph)),Tuple{T},(:src,:tgt)}

end
