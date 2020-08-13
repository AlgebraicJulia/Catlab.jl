module ACSets
export Schema, SchemaExpr, DataExpr, AttrExpr, FreeSchema,
  CatDesc, CatDescType, AttrDesc, AttrDescType, AbstractACSet, ACSet,
  nparts, add_part!, add_parts!, _add_parts!, subpart, incident, set_subpart!, set_subparts!,
  TheoryGraph, AbstractGraph, Graph,
  TheoryDecGraph, AbstractDecGraph, DecGraph

using Catlab.GAT, Catlab.Syntax, Catlab.Present, Catlab.Theories
using StructArrays
using MLStyle

@theory Category(Ob,Hom) => Schema(Ob,Hom,Data,Attr) begin
  Data::TYPE
  Attr(dom::Ob,codom::Data)::TYPE

  compose(f::Hom(A,B), g::Attr(B,X))::Attr(A,X) ⊣ (A::Ob, B::Ob, X::Data)
  (compose(f, compose(g, a)) == compose(compose(f, g), a)
    ⊣ (A::Ob, B::Ob, C::Ob, X::Data, f::Hom(A,B), g::Hom(B,C), a::Attr(C, X)))
  compose(id(A), a) == a ⊣ (A::Ob, X::Ob, a::Attr(A,X))
end

abstract type SchemaExpr{T} <: GATExpr{T} end
abstract type DataExpr{T} <: SchemaExpr{T} end
abstract type AttrExpr{T} <: SchemaExpr{T} end

@syntax FreeSchema(ObExpr,HomExpr,DataExpr,AttrExpr) Schema begin
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

function Base.getproperty(AD::Type{T},i::Symbol) where
  {Ob,Hom,Dom,Codom,T<:CatDesc{Ob,Hom,Dom,Codom}}
  @match i begin
    :ob => Ob
    :hom => Hom
    :dom => Dom
    :codom => Codom
    _ => getfield(AD,i)
  end
end

function cd_ob_num(CD::Type{T}, ob::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Ob .== ob)::Int
end

function cd_hom_num(CD::Type{T}, hom::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  findfirst(Hom .== hom)::Int
end

function cd_dom(CD::Type{T}, hom::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[Dom[cd_hom_num(CD,hom)]]
end

function cd_codom(CD::Type{T}, hom::Symbol) where {Ob,Hom,Dom,Codom, T <: CatDesc{Ob,Hom,Dom,Codom}}
  Ob[Codom[cd_hom_num(CD,hom)]]
end

struct AttrDesc{CD,Data,Attr,ADom,ACodom}
  function AttrDesc{CD,Data,Attr,ADom,ACodom}() where {CD,Data,Attr,ADom,ACodom}
    new{CD,Data,Attr,ADom,ACodom}()
  end
  function AttrDesc(pres::Presentation{Schema})
    CD = CatDescType(pres)
    datas, attrs = generators(pres, :Data), generators(pres,:Attr)
    data_syms, attr_syms = nameof.(datas), nameof.(attrs)
    ob_num = ob -> findfirst(CD.ob .== ob)::Int
    data_num = ob -> findfirst(data_syms .== ob)::Int
    new{CD,Tuple(data_syms), Tuple(attr_syms),
        Tuple(@. ob_num(nameof(dom(attrs)))), Tuple(@. data_num(nameof(codom(attrs))))}()
  end
  function AttrDesc(::CatDesc{Ob,Hom,Dom,Codom}) where {Ob,Hom,Dom,Codom}
    new{CatDesc{Ob,Hom,Dom,Codom},(),(),(),()}
  end
end

AttrDescType(pres::Presentation{Schema}) = typeof(AttrDesc(pres))

function Base.getproperty(AD::Type{T}, i::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  @match i begin
    :cd => CD
    :data => Data
    :attr => Attr
    :adom => ADom
    :acodom => ACodom
    _ => getfield(AD,i)
  end
end

function ad_data_num(AD::Type{T}, data::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  findfirst(Data .== data)::Int
end

function ad_attr_num(AD::Type{T}, attr::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  findfirst(Attr .== attr)::Int
end

function ad_dom(AD::Type{T}, attr::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  CD.ob[ADom[ad_attr_num(AD,attr)]]
end

function ad_codom(AD::Type{T}, attr::Symbol) where
  {CD,Data,Attr,ADom,ACodom,T <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  Data[ACodom[ad_attr_num(AD,attr)]]
end

function ad_codom_data_type(Ts::Type{T}, AD::Type{S}, attr::Symbol) where
  {T <: Tuple, CD,Data,Attr,ADom,ACodom,S <: AttrDesc{CD,Data,Attr,ADom,ACodom}}
  fieldtypes(Ts)[ACodom[ad_attr_num(AD,attr)]]
end


function make_index(CD::Type{<:CatDesc},AD::Type{<:AttrDesc},Ts::Type{<:Tuple},Idxed::Tuple)
  function make_idx(name)
    if name ∈ CD.hom
      Vector{Vector{Int}}()
    elseif name ∈ AD.attr
      Dict{ad_codom_data_type(Ts,AD,name),Vector{Int}}()
    else
      error("invalid index parameter")
    end
  end
  NamedTuple{Idxed}(Tuple(make_idx(name) for name in Idxed))
end

function table_desc(::Type{CatDesc{Ob,Hom,Dom,Codom}},
                    ::Type{AttrDesc{CatDesc{Ob,Hom,Dom,Codom},Data,Attr,ADom,ACodom}},
                    ts::Tuple) where {Ob,Hom,Dom,Codom,Data,Attr,ADom,ACodom}
  cols = [Tuple{Symbol,DataType}[] for ob in Ob]
  for i in 1:length(Hom)
    push!(cols[Dom[i]], (Hom[i],Int))
  end
  for i in 1:length(Attr)
    push!(cols[ADom[i]], (Attr[i],ts[ACodom[i]]))
  end
  [(col_names = first.(cols[i]), col_types = last.(cols[i])) for i in 1:length(Ob)]
end

abstract type AbstractAttributedCSet{CD,AD,Ts} end

const AbstractACSet = AbstractAttributedCSet

struct AttributedCSet{CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed,
             TablesType <: NamedTuple, IndexType <: NamedTuple} <: AbstractACSet{CD,AD,Ts}
  tables::TablesType
  index::IndexType
  function AttributedCSet{CD}() where {CD <: CatDesc}
    ACSet{CD,typeof(AttrDesc(CD())),Tuple{}}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed}() where {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple, Idxed}
    td = table_desc(CD,AD,Tuple(Ts.parameters))
    empty_tables = NamedTuple{CD.ob}(
      [StructArray{NamedTuple{Tuple(td[i].col_names), Tuple{td[i].col_types...}}}(undef,0)
       for i in 1:length(CD.ob)])
    index = make_index(CD,AD,Ts,Idxed)
    new{CD,AD,Ts,Idxed,typeof(empty_tables),typeof(index)}(empty_tables,index)
  end
  function AttributedCSet{CD,AD,Ts,Idxed,TT,IT}() where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    ACSet{CD,AD,Ts,Idxed}()
  end
  function AttributedCSet{CD,AD,Ts,Idxed,TT,IT}(tables::TT,index::IT) where
    {CD <: CatDesc, AD <: AttrDesc{CD}, Ts <: Tuple,Idxed,TT <: NamedTuple,IT <: NamedTuple}
    new{CD,AD,Ts,Idxed,TT,IT}(tables,index)
  end
end

const ACSet = AttributedCSet

function fieldtype(::Type{T},i::Integer) where {T <: NamedTuple}
  fieldtypes(T)[i]
end

function fieldtype(::Type{T},s::Symbol) where {T <: NamedTuple}
  i = findfirst(fieldnames(T) .== s)
  fieldtype(T,i)
end

function Base.fieldnames(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fieldnames(eltype(T))
end

function Base.fieldtypes(::Type{T}) where {T <: StructArray{<:NamedTuple}}
  fieldtypes(eltype(T))
end

function fieldtype(::Type{T},i::Integer) where {T <: StructArray{<:NamedTuple}}
  fieldtype(eltype(T),i)
end

function fieldtype(::Type{T},s::Symbol) where {T <: StructArray{<:NamedTuple}}
  fieldtype(eltype(T),s)
end

function Base.:(==)(x1::T, x2::T) where T <: ACSet
  x1.tables == x2.tables
end

function Base.copy(ins::T) where T <: ACSet
  T(copy(ins.tables),copy(ins.index))
end

Base.empty(ins::T) where T <: ACSet = T()

function Base.show(io::IO, mime::MIME"text/plain", ins::AbstractACSet{CD,AD,Ts}) where {CD,AD,Ts}
  println(io,"ACSet")
  for ob in CD.ob
    println(io, "  $ob = 1:$(nparts(ins,ob))")
  end
  for (i,hom) in enumerate(CD.hom)
    println(io, "  $hom : $(CD.ob[CD.dom[i]]) → $(CD.ob[CD.codom[i]])")
    println(io, "    $(subpart(ins,hom))")
  end
  for (i,conc) in enumerate(AD.data)
    println(io, "  $conc = $(Ts.parameters[i])")
  end
  for (i,attr) in enumerate(AD.attr)
    println(io, "  $attr : $(CD.ob[AD.adom[i]]) ⇒ $(AD.data[AD.acodom[i]])")
    println(io, "    $(subpart(ins,attr))")
  end
end

nparts(ins::ACSet,type::Symbol) = length(ins.tables[type])

haspart(ins::ACSet,type::Symbol,part::Int) = 1 <= part <= nparts(ins,type)

""" Insert into sorted vector, preserving the sorting.
"""
function insertsorted!(a::AbstractVector, x)
  insert!(a, searchsortedfirst(a, x), x)
end

""" Delete one occurrence of value from sorted vector.
"""
function deletesorted!(a::AbstractVector, x)
  i = searchsortedfirst(a, x)
  @assert i <= length(a) && a[i] == x "Value $x is not contained in $a"
  deleteat!(a, i)
end

add_part!(ins::ACSet,type::Symbol,subparts::NamedTuple) =
  _add_parts!(ins,Val(type),StructArray([subparts]))[1]
add_parts!(ins::ACSet,type::Symbol,subpartses::StructArray{<:NamedTuple}) =
  _add_parts!(ins,Val(type),subpartses)

@generated function _add_parts!(ins::ACSet{CD,AD,Ts,Idxed,TT},::Val{ob},
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
  for hom in fieldnames(T)
    if hom ∈ Idxed
      if hom ∈ CD.hom
        index_code = quote
          @assert haspart(ins, $(Expr(:quote, cd_codom(CD,hom))), subparts.$hom)
          insertsorted!(ins.index.$(hom)[subparts.$hom],i)
        end
        push!(inner_loop.args, index_code)
      elseif hom ∈ AD.attr
        index_code = quote
          if subparts.$hom ∈ keys(ins.index.$hom)
            insertsorted!(ins.index.$(hom)[subparts.$hom],i)
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

subpart(ins::ACSet, part, name::Symbol) = subpart(ins,name)[part]
subpart(ins::ACSet, name::Symbol) = _subpart(ins,Val(name))

@generated function _subpart(ins::ACSet{CD,AD,Ts},::Val{name}) where {CD,AD,Ts,name}
  if name ∈ CD.hom
    dom = cd_dom(CD,name)
    :(ins.tables.$dom.$name)
  elseif name ∈ AD.attr
    dom = ad_dom(AD,name)
    :(ins.tables.$dom.$name)
  else
    throw(KeyError(name))
  end
end

incident(ins::ACSet, part, name::Symbol) = _incident(ins, part, Val(name))

get_data_index(d::AbstractDict{K,Int}, k::K) where K =
  get(d, k, nothing)
get_data_index(d::AbstractDict{K,<:AbstractVector{Int}}, k::K) where K =
  get(d, k, 1:0)

@generated function _incident(ins::ACSet{CD,AD,Ts,Idxed}, part, ::Val{name}) where {CD,AD,Ts,Idxed,name}
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

@generated function _set_subpart!(ins::ACSet{CD,AD,Ts,Idxed}, part::Int, ::Val{name}, subpart) where
  {CD,AD,Ts,Idxed,name}
  code = Expr(:block)
  if name ∈ CD.hom
    push!(code.args, quote
          old = ins.tables.$(cd_dom(CD,name)).$(name)[part]
          ins.tables.$(cd_dom(CD,name)).$name[part] = subpart
          end)
  elseif name ∈ AD.attr
    push!(code.args, quote
          old = ins.tables.$(ad_dom(AD,name)).$(name)[part]
          ins.tables.$(ad_dom(AD,name)).$name[part] = subpart
          end)
  else
    throw(KeyError(name))
  end
  if name ∈ Idxed
    if name ∈ CD.hom
      index_code = quote
        @assert haspart(ins,$(Expr(:quote, cd_codom(CD,name))),subpart)
        deletesorted!(ins.index.$(name)[old], part)
        insertsorted!(ins.index.$(name)[subpart], part)
      end
      push!(code.args, index_code)
    elseif name ∈ AD.attr
      index_code = quote
        @assert pop!(ins.index.$name, old) == part
        insertsorted!(get!(ins.index.$name, subpart) do; Int[] end, part)
      end
      push!(code.args, index_code)
    end
  end
  code
end

set_subpart!(ins::ACSet, part, name, subpart) = _set_subpart!(ins, part, Val(name), subpart)

function set_subparts!(ins::ACSet, part, subparts)
  for (name, subpart) in pairs(subparts)
    set_subpart!(ins, part, name, subpart)
  end
end

@present TheoryGraph(FreeSchema) begin
  V::Ob
  E::Ob

  src::Hom(E,V)
  tgt::Hom(E,V)
end

const AbstractGraph = AbstractACSet{typeof(CatDesc(TheoryGraph))}

const Graph = ACSet{typeof(CatDesc(TheoryGraph)),
                    typeof(AttrDesc(TheoryGraph)),Tuple{},(:src,:tgt)}

@present TheoryDecGraph <: TheoryGraph begin
  X::Data

  vdec::Attr(V,X)
  edec::Attr(E,X)
end

const AbstractDecGraph{T} = AbstractACSet{typeof(CatDesc(TheoryDecGraph)),
                                          typeof(AttrDesc(TheoryDecGraph)),Tuple{T}}

const DecGraph{T} = ACSet{typeof(CatDesc(TheoryDecGraph)),
                          typeof(AttrDesc(TheoryDecGraph)),Tuple{T},(:src,:tgt,:vdec)}

end
