module CSetDataStructures
export @acset_type, @abstract_acset_type, @declare_schema, FreeSchema,
  StructACSet, DynamicACSet, SimpleACSet, AnonACSet, StructCSet, ACSetTableType

using MLStyle
using LabelledArrays
using Reexport
using CompTime
import Tables

@reexport using ..ACSetInterface
using ..ACSetColumns
using ..IndexUtils
using ...Theories, ...Present, ...Syntax
using ...Theories: FreeSchema, SchemaDesc, SchemaDescType, CSetSchemaDescType,
  SchemaDescTypeType, ob_num, codom_num, attr, attrtype
import ...Present: Presentation

# StructACSet Struct Generation
###############################

# ACSets that use a particular data layout: i.e. "parts" and "subparts"
abstract type SimpleACSet <: ACSet end

abstract type StructACSet{S<:SchemaDescType,Ts<:Tuple} <: SimpleACSet end

const StructCSet = StructACSet{S,Tuple{}} where
  {S<:CSetSchemaDescType}

q(s::Symbol) = s
q(s::GATExpr) = nameof(s)

""" Creates a type used for `StructACSet`s
"""
function pi_type(dom::Vector, F::Function)
  NamedTuple{Tuple(q.(dom)),Tuple{F.(dom)...}}
end

""" Creates a quoted element of a named tuple used for `StructACSet`s
"""
function pi_type_elt(dom::Vector, f::Function)
  if length(dom) > 0
    Expr(:tuple, Expr(:parameters, [Expr(:kw, nameof(d), f(d)) for d in dom]...))
  else # workaround for Julia 1.0
    :(NamedTuple())
  end
end

function genericize(T::Type, tvars::Vector{TypeVar})
  occuring_variables = []
  cur = T
  for tvar in reverse(tvars)
    next = UnionAll(tvar, cur)
    if typeof(next) == UnionAll && next.var == tvar
      push!(occuring_variables, tvar)
      cur = next
    end
  end
  if length(occuring_variables) > 0
    :($cur{$([tvar.name for tvar in reverse(occuring_variables)]...)})
  else
    cur
  end
end

function struct_acset(name::Symbol, parent, p::Presentation{ThSchema};
                      index = [], unique_index = [])
  homs = p.generators[:Hom]
  attrs = p.generators[:Attr]
  function column_type(f)
    if f ∈ homs
      if nameof(f) ∈ index
        IndexedVector{Int,Vector{Vector{Int}}}
      elseif nameof(f) ∈ unique_index
        IndexedVector{Int,Vector{Int}}
      else
        Vector{Int}
      end
    elseif f ∈ attrs
      if nameof(f) ∈ index
        IndexedVector{T,Dict{T,Vector{Int}}} where {T}
      elseif nameof(f) ∈ unique_index
        IndexedVector{T,Dict{T,Int}} where {T}
      else
        Vector{T} where {T}
      end
    end
  end
  struct_acset(name, parent, p,
               Dict{Symbol,Type}([nameof(f) => column_type(f) for f in vcat(homs,attrs)]))
end

""" Create the struct declaration for a `StructACSet` from a Presentation
"""
function struct_acset(name::Symbol, parent, p::Presentation{ThSchema},
                      column_types::Dict{Symbol,Type})
  obs = p.generators[:Ob]
  homs = p.generators[:Hom]
  attrtypes = p.generators[:AttrType]
  Ts = nameof.(attrtypes)
  Tvars = Dict{Symbol,TypeVar}(name => TypeVar(name) for name in Ts)
  attrs = p.generators[:Attr]
  function subpart_type(f)
    if f ∈ attrs
      T = Tvars[nameof(codom(f))]
      if nameof(f) ∈ keys(column_types)
        column_types[nameof(f)]{T}
      else
        Vector{T}
      end
    elseif f ∈ homs
      if nameof(f) ∈ keys(column_types)
        column_types[nameof(f)]
      else
        Vector{Int}
      end
    end
  end
  parameterized_type, new_call = if length(attrtypes) > 0
    (:($name{$(Ts...)}), :(new{$(Ts...)}))
  else
    name, :new
  end
  schema_type = SchemaDescTypeType(p)
  parts_t = :($(GlobalRef(LabelledArrays, :LArray)){
    Int64, 1, Vector{Int64}, $(Tuple([nameof.(obs)...]))
  })
  subparts_t = genericize(pi_type(vcat(homs,attrs), subpart_type),TypeVar[values(Tvars)...])
  quote
    struct $parameterized_type <: $parent{$schema_type, Tuple{$(Ts...)}}
      parts::$parts_t
      subparts::$subparts_t
      function $parameterized_type() where {$(nameof.(attrtypes)...)}
        $new_call(
          $parts_t(zeros(Int, $(length(obs)))),
          $(pi_type_elt(vcat(homs,attrs), f -> :($(genericize(subpart_type(f), TypeVar[values(Tvars)...]))())))
        )
      end
      function $parameterized_type(parts::$parts_t, subparts::$subparts_t) where {$(nameof.(attrtypes)...)}
        $new_call(parts, subparts)
      end
    end
  end
end

unquote(x::QuoteNode) = x.value

macro acset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructACSet))
  end
  name, schema, idx_args = @match head begin
    Expr(:call, name, schema, idx_args...) => (name, schema, idx_args)
    _ => error("Unsupported head for @acset_type")
  end
  quote
    $(esc(:eval))($(GlobalRef(CSetDataStructures, :struct_acset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema));
      $((esc(arg) for arg in idx_args)...)))
    Core.@__doc__ $(esc(name))
  end
end

macro abstract_acset_type(head)
  type, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(CSetDataStructures, :StructACSet))
  end
  esc(quote
    abstract type $type{S,Ts} <: $parent{S,Ts} end
  end)
end

function column_type(s, f, attrtypes, index, unique_index)
  if f ∈ s.homs
    if f ∈ index
      IndexedVector{Int,Vector{Vector{Int}}}
    elseif f ∈ unique_index
      IndexedVector{Int,Vector{Int}}
    else
      Vector{Int}
    end
  elseif f ∈ s.attrs
    codom = attrtypes[s.codoms[f]]
    if f ∈ index
      IndexedVector{codom,Dict{codom, Vector{Int}}}
    elseif f ∈ unique_index
      IndexedVector{codom,Dict{codom,Int}}
    else
      Vector{codom}
    end
  end
end

struct DynamicACSet <: SimpleACSet
  name::String
  schema::SchemaDesc
  attrtypes::Dict{Symbol,Type}
  parts::Dict{Symbol,Int}
  subparts::Dict{Symbol, AbstractVector}
  function DynamicACSet(
    name::String,
    p::Presentation;
    attrtypes=Dict{Symbol,Type}(),
    index::Vector{Symbol}=Symbol[],
    unique_index::Vector{Symbol}=Symbol[]
  )
    s = SchemaDesc(p)

    new(
      name,
      s,
      attrtypes,
      Dict(ob => 0 for ob in s.obs),
      Dict(f => column_type(s,f,attrtypes,index,unique_index)() for f in [s.homs; s.attrs])
    )
  end
  function DynamicACSet(
    name::String,
    schema::SchemaDesc,
    attrtypes::Dict{Symbol,Type},
    parts::Dict{Symbol,Int},
    subparts::Dict{Symbol,AbstractVector}
  )
    new(name,schema,attrtypes,parts,subparts)
  end
end

struct AnonACSet{S,Ts,Parts,Subparts} <: StructACSet{S,Ts}
  parts::Parts
  subparts::Subparts
  function AnonACSet{S,Ts,Parts,Subparts}(
    parts::Parts,
    subparts::Subparts
  ) where {S,Ts,Parts,Subparts}
    new{S,Ts,Parts,Subparts}(parts,subparts)
  end

  function AnonACSet{S,Ts,Parts,Subparts}() where {S,Ts,Parts,Subparts}
    new{S,Ts,Parts,Subparts}(
      Parts(zeros(Int64, length(S.parameters[1]))),
      Subparts(T() for T in Subparts.parameters[2].parameters)
    )
  end

  function AnonACSet(
    p::Presentation;
    attrtypes=Dict{Symbol,Type}(),
    index::Vector{Symbol}=Symbol[],
    unique_index::Vector{Symbol}=Symbol[]
  )
    T = AnonACSetType(p; attrtypes=attrtypes, index=index, unique_index=unique_index)
    T()
  end
end

function AnonACSetType(
  s::SchemaDesc;
  attrtypes::Dict{Symbol, Type}=Dict{Symbol,Type}(),
  index::Vector{Symbol}=Symbol[],
  unique_index::Vector{Symbol}=Symbol[],
  union_all::Bool=false
)
  (!union_all || isempty(attrtypes)) || error("If union_all is true, then attrtypes must be empty")
  S = SchemaDescTypeType(s)
  if union_all
    type_vars = [TypeVar(at) for at in s.attrtypes]
    attrtypes = Dict(zip(s.attrtypes, type_vars))
  else
    type_vars = [attrtypes[at] for at in s.attrtypes]
  end
  Ts = Tuple{type_vars...}
  Parts = LArray{Int64, 1, Vector{Int64}, (s.obs...,)}
  Subparts = NamedTuple{
    ([s.homs; s.attrs]...,),
    Tuple{(column_type(s,f,attrtypes,index,unique_index) for f in [s.homs; s.attrs])...}
  }
  T = AnonACSet{S,Ts,Parts,Subparts}
  if union_all
    foldr(UnionAll, type_vars; init=T)
  else
    T
  end
end

function AnonACSetType(
  p::Presentation;
  attrtypes::Dict{Symbol, Type}=Dict{Symbol,Type}(),
  index::Vector{Symbol}=Symbol[],
  unique_index::Vector{Symbol}=Symbol[],
  union_all::Bool=false
)
  AnonACSetType(SchemaDesc(p); attrtypes, index, unique_index, union_all)
end


function ACSetTableDesc(::Type{S}, ob::Symbol) where {S}
  s = SchemaDesc(S)
  attrs = filter(s.attrs) do attr
    s.doms[attr] == ob
  end
  doms = filter(s.doms) do (f,i)
    f ∈ attrs
  end
  codoms = filter(s.codoms) do (f,i)
    f ∈ attrs
  end
  SchemaDesc([ob], Symbol[], s.attrtypes, attrs, doms, codoms)
end

function ACSetTableDataType(::Type{<:StructACSet{S,Ts}}, ob::Symbol) where {S,Ts}
  s = SchemaDesc(S)
  s′ = ACSetTableDesc(S,ob)
  attrtypes = Dict{Symbol, Type}(a => T for (a,T) in zip(s.attrtypes, Ts.parameters))
  AnonACSetType(s′;attrtypes)
end

function ACSetTableUnionAll(::Type{<:StructACSet{S}}, ob::Symbol) where {S}
  s′ = ACSetTableDesc(S,ob)
  AnonACSetType(s′;union_all=true)
end

function ACSetTableType(X::Type, ob::Symbol; union_all::Bool=false)
  (union_all ? ACSetTableUnionAll : ACSetTableDataType)(X, ob)
end

Base.copy(acs::DynamicACSet) =
  DynamicACSet(acs.name,acs.schema,acs.attrtypes,copy(acs.parts), deepcopy(acs.subparts))

Base.copy(acs::T) where {T <: StructACSet} = T(copy(acs.parts), map(copy, acs.subparts))

Base.:(==)(acs1::T, acs2::T) where {T <: SimpleACSet} =
  acs1.parts == acs2.parts && acs1.subparts == acs2.subparts

ACSetInterface.acset_schema(acs::StructACSet{S}) where {S} = SchemaDesc(S)
ACSetInterface.acset_schema(acs::DynamicACSet) = acs.schema

add_parts_with_indices!(acs::SimpleACSet, ob::Symbol, n::Int, index_sizes::NamedTuple) =
  add_parts!(acs, ob, n)

ACSetInterface.add_parts!(acs::StructACSet{S}, type::Symbol, n::Int) where {S} =
  _add_parts!(acs, Val{S}, Val{type}, n)

ACSetInterface.add_parts!(acs::DynamicACSet, type::Symbol, n::Int) =
  runtime(_add_parts!, acs, acs.schema, type, n)

@ct_enable function _add_parts!(acs::SimpleACSet, @ct(S), @ct(ob), n::Int)
  @ct s = SchemaDesc(S)
  m = acs.parts[@ct ob]
  nparts = m + n
  newparts = (m+1):nparts
  acs.parts[@ct ob] = nparts

  @ct_ctrl for f in vcat(s.homs,s.attrs)
    @ct_ctrl if s.doms[f] == ob
      resize_clearing!(acs.subparts[@ct f], nparts)
    end
    @ct_ctrl if s.codoms[f] == ob
      codom_hint!(acs.subparts[@ct f], nparts)
    end
  end

  newparts
end

ACSetInterface.nparts(acs::SimpleACSet, type::Symbol) = acs.parts[type]

ACSetInterface.has_part(acs::StructACSet{S}, ob::Symbol) where {S} =
  _has_part(Val{S}, Val{ob})

ACSetInterface.has_part(acs::DynamicACSet, ob::Symbol) =
  runtime(_has_part, acs.schema, ob)

@ct_enable function _has_part(@ct(S), @ct(ob))
  @ct s = SchemaDesc(S)
  @ct ob ∈ s.obs
end

outgoing(acs::StructACSet{S}, ob::Symbol) where {S} = _outgoing(Val{S}, Val{ob})

outgoing(acs::DynamicACSet, ob::Symbol) = runtime(_outgoing, acs.schema, ob)

@ct_enable function _outgoing(@ct(S), @ct(ob))
  @ct s = SchemaDesc(S)
  @ct Tuple(filter(f -> s.doms[f] == ob, vcat(s.homs,s.attrs)))
end

ACSetInterface.subpart(acs::SimpleACSet, f::Symbol) = values(acs.subparts[f])

ACSetInterface.subpart(acs::SimpleACSet, part::Int, f::Symbol) = acs.subparts[f][part]

ACSetInterface.has_subpart(acs::StructACSet{S}, f::Symbol) where {S} =
  _has_subpart(Val{S}, Val{f})

ACSetInterface.has_subpart(acs::DynamicACSet, f::Symbol) =
  runtime(_has_subpart, acs.schema, f)

@ct_enable function _has_subpart(@ct(S), @ct(f))
  @ct s = SchemaDesc(S)
  @ct f ∈ [s.homs; s.attrs]
end

ACSetInterface.incident(acs::SimpleACSet, part, f::Symbol) = preimage(acs.subparts[f], part)
ACSetInterface.incident(acs::SimpleACSet, parts::Union{AbstractVector,UnitRange}, f::Symbol) =
  preimage_multi(acs.subparts[f], parts)
ACSetInterface.incident(acs::StructACSet{S}, ::Colon, f::Symbol) where {S} =
  _incident(acs, Val{S}, :, Val{f})

ACSetInterface.incident(acs::DynamicACSet, ::Colon, f::Symbol) where {S} =
  runtime(_incident, acs, acs.schema, :, f)

@ct_enable function _incident(acs::SimpleACSet, @ct(S), ::Colon, @ct(f))
  @ct s = SchemaDesc(S)
  incident(acs, parts(acs, @ct(s.codoms[f])), @ct(f))
end

ACSetInterface.set_subpart!(acs::StructACSet{S}, part::Int, f::Symbol, subpart) where {S} =
  _set_subpart!(acs, Val{S}, part, Val{f}, subpart)

ACSetInterface.set_subpart!(acs::DynamicACSet, part::Int, f::Symbol, subpart) =
  runtime(_set_subpart!, acs, acs.schema, part, f, subpart)

@ct_enable function _set_subpart!(acs::SimpleACSet, @ct(S), part, @ct(f), subpart)
  @ct s = SchemaDesc(S)
  @ct_ctrl if f ∈ s.homs
    @assert 0 <= subpart <= acs.parts[@ct s.codoms[f]]
  end
  acs.subparts[@ct f][part] = subpart
end

ACSetInterface.clear_subpart!(acs::SimpleACSet, part::Int, f::Symbol) =
  clear_index!(acs.subparts[f], part)

ACSetInterface.rem_part!(acs::StructACSet{S}, type::Symbol, part::Int) where {S} =
  _rem_part!(acs, Val{S}, Val{type}, part)

ACSetInterface.rem_part!(acs::DynamicACSet, type::Symbol, part::Int) =
  runtime(_rem_part!, acs, acs.schema, type, part)

@ct_enable function _rem_part!(acs::SimpleACSet, @ct(S), @ct(ob), part)
  @ct s = SchemaDesc(S)
  @ct in_homs = filter(hom -> s.codoms[hom] == ob, s.homs)
  @ct out_homs = filter(f -> s.doms[f] == ob, s.homs)
  @ct out_attrs = filter(f -> s.doms[f] == ob, s.attrs)

  last_part = acs.parts[@ct ob]

  @ct_ctrl for hom in in_homs
    incoming_to_part = copy(incident(acs, part, @ct hom))
    # Nasty unique_indexing bs
    if incoming_to_part != 0
      clear_subpart!(acs, incoming_to_part, @ct hom)
    end

    incoming_to_last_part = copy(incident(acs, last_part, @ct hom))
    if incoming_to_last_part != 0
      set_subpart!(acs, incoming_to_last_part, (@ct hom), part)
    end

    codom_hint!(acs.subparts[@ct hom], last_part - 1)
  end

  @ct_ctrl for f in [out_homs; out_attrs]
    if isassigned(acs.subparts[@ct f], last_part)
      set_subpart!(acs, part, (@ct f), subpart(acs, last_part, @ct f))
    end
    clear_subpart!(acs, last_part, @ct f)
    resize_clearing!(acs.subparts[@ct f], last_part - 1)
  end

  acs.parts[@ct ob] -= 1
end

# Copy Parts
############

@ct_enable function common_objects(@ct(S), @ct(S′))
  @ct s,s′ = SchemaDesc(S), SchemaDesc(S′)
  @ct Tuple(intersect(s.obs, s′.obs))
end

ACSetInterface.copy_parts!(to::StructACSet{S}, from::StructACSet{S′}) where {S,S′} =
  copy_parts!(to, from, common_objects(Val{S}, Val{S′}))

ACSetInterface.copy_parts!(to::DynamicACSet, from::DynamicACSet) =
  copy_parts!(to, from, runtime(common_objects, to.schema, from.schema))

ACSetInterface.copy_parts!(to::SimpleACSet, from::SimpleACSet; kw...) =
  copy_parts!(to, from, (;kw...))

ACSetInterface.copy_parts!(to::SimpleACSet, from::SimpleACSet, obs::Tuple) =
  copy_parts!(to, from, NamedTuple{obs}((:) for ob in obs))

ACSetInterface.copy_parts!(to::StructACSet{S}, from::StructACSet{S′}, parts::NamedTuple) where {S,S′} =
  _copy_parts!(to, Val{S}, from, Val{S′}, replace_colons(from, parts))

ACSetInterface.copy_parts!(to::DynamicACSet, from::DynamicACSet, parts::NamedTuple) =
  runtime(_copy_parts!, to, to.schema, from, from.schema, replace_colons(from, parts))

@ct_enable function _copy_parts!(
  to::SimpleACSet, @ct(S),
  from::SimpleACSet, @ct(S′),
  parts::NamedTuple{obs}
) where {obs}

  @ct begin
    s, s′ = SchemaDesc(S), SchemaDesc(S′)
    @assert obs ⊆ intersect(s.obs, s′.obs)
    homs = intersect(s.homs, s′.homs)
    homs = filter(homs) do hom
      c, c′, d, d′ = s.doms[hom], s′.doms[hom], s.codoms[hom], s′.codoms[hom]
      c == c′ && d == d′ && c ∈ obs && d ∈ obs
    end
    hom_triples = [ (hom, s.doms[hom], s.codoms[hom]) for hom in homs ]
    in_obs = unique!(map(last, hom_triples))
  end

  newparts = copy_parts_only!(to, from, parts)
  partmaps = NamedTuple{@ct Tuple(in_obs)}(((@ct_ctrl (
    Dict{Int,Int}(zip(parts[@ct type], newparts[@ct type]))
    for type in in_obs
  )...),))

  @ct_ctrl for (name, dom, codom) in hom_triples
    for (p, newp) in zip(parts[@ct dom], newparts[@ct dom])
      q = subpart(from, p, @ct name)
      newq = get(partmaps[@ct codom], q, nothing)
      if !isnothing(newq)
        set_subpart!(to, newp, @ct(name), newq)
      end
    end
  end

  newparts
end

ACSetInterface.copy_parts_only!(to::SimpleACSet, from::SimpleACSet; kw...) =
  copy_parts!(to, from, (;kw...))

ACSetInterface.copy_parts_only!(to::StructACSet{S}, from::StructACSet{S′}) where {S,S′} =
  copy_parts_only!(to, from, common_objects(Val{S}, Val{S′}))

ACSetInterface.copy_parts_only!(to::SimpleACSet, from::SimpleACSet, obs::Tuple) =
  copy_parts_only!(to, from, NamedTuple{obs}((:) for ob in obs))

ACSetInterface.copy_parts_only!(to::StructACSet{S}, from::StructACSet{S′}, parts::NamedTuple) where {S,S′}=
  _copy_parts_only!(to, Val{S}, from, Val{S′}, replace_colons(from, parts))

ACSetInterface.copy_parts_only!(to::DynamicACSet, from::DynamicACSet, parts::NamedTuple) =
  runtime(_copy_parts_only!, to, to.schema, from, from.schema, replace_colons(from, parts))

@ct_enable function _copy_parts_only!(
  to::SimpleACSet, @ct(S),
  from::SimpleACSet, @ct(S′),
  parts::NamedTuple{obs}
) where {obs}

  @ct begin
    s, s′ = SchemaDesc(S), SchemaDesc(S′)
    @assert obs ⊆ intersect(s.obs, s′.obs)
    attrs = intersect(s.attrs, s′.attrs)
    attrs = filter(attrs) do attr
      ob, ob′ = s.doms[attr], s′.doms[attr]
      ob == ob′ && ob ∈ obs
    end
  end

  newparts = NamedTuple{@ct obs}((@ct_ctrl(
    (add_parts!(to, @ct(ob), length(parts[@ct ob])) for ob in obs)...
  ),))

  @ct_ctrl for a in attrs
    @ct ob = s.doms[a]
    set_subpart!(to, newparts[@ct ob], @ct(a), subpart(from, parts[@ct ob], @ct(a)))
  end

  newparts
end

function replace_colons(acs::ACSet, parts::NamedTuple{types}) where {types}
  NamedTuple{types}(map(types, parts) do type, part
    part == (:) ? (1:nparts(acs, type)) : part
  end)
end


# Printing
##########

ACSetInterface.acset_name(x::StructACSet) = sprint(show, typeof(x))

function ACSetInterface.acset_name(x::DynamicACSet)
  s = x.schema
  if length(s.attrtypes) == 0
    x.name
  else
    Ts = join([x.attrtypes[at] for at in s.attrtypes], ",")
    "$(x.name){$(Ts)}"
  end
end

function Base.show(io::IO, acs::SimpleACSet)
  s = acset_schema(acs)
  if get(io, :compact, false)
    print(io, acset_name(acs))
    print(io, " {")
    join(io, ("$ob = $(nparts(acs,ob))" for ob in s.obs), ", ")
    print(io, "}")
  else
    print(io, acset_name(acs))
    println(io, ":")
    join(io, Iterators.flatten((
      ("  $ob = $(parts(acs,ob))" for ob in s.obs),
      ("  $f : $(s.doms[f]) → $(s.codoms[f]) = $(subpart(acs,f))"
       for f in s.homs),
      ("  $a : $(s.doms[a]) → $(s.codoms[a]) = $(subpart(acs,a))"
       for a in s.attrs),
    )), "\n")
  end
end

# Tables
########

struct ACSetTable{T<:ACSet, ob} <: Tables.AbstractColumns
  parent::T
end

ACSetTable(acs::ACSet, ob::Symbol) = ACSetTable{typeof(acs), ob}(acs)

ACSetInterface.tables(acs::StructACSet{<:SchemaDescType{obs}}) where {obs} =
  NamedTuple([ob => ACSetTable(acs, ob) for ob in obs])

ACSetInterface.tables(acs::DynamicACSet) =
  NamedTuple([ob => ACSetTable(acs, ob) for ob in acs.schema.obs])

parent(sat::ACSetTable) = getfield(sat, :parent)

struct ACSetRow{T<:ACSet, ob} <: Tables.AbstractRow
  parent::T
  idx::Int
end

parent(row::ACSetRow) = getfield(row, :parent)
idx(row::ACSetRow) = getfield(row, :idx)

# - Tables.jl interface

Tables.istable(sat::ACSetTable) = true

Tables.columnaccess(sat::ACSetTable) = true
Tables.columns(sat::ACSetTable) = sat

Tables.getcolumn(sat::ACSetTable{T,ob}, i::Int) where {T,ob} =
  Base.getproperty(sat, outgoing(parent(sat), ob)[i])

Base.getproperty(sat::ACSetTable, nm::Symbol) = subpart(parent(sat), :, nm)

Tables.getcolumn(sat::ACSetTable, nm::Symbol) = Base.getproperty(sat, nm)

Base.propertynames(sat::ACSetTable{T,ob}) where {T,ob} = outgoing(parent(sat), ob)

Tables.columnnames(sat::ACSetTable) = Base.propertynames(sat)

Tables.rowaccess(sat::ACSetTable) = true
Tables.rows(sat::ACSetTable{T,ob}) where {T,ob} =
  ACSetRow{T,ob}.(Ref(parent(sat)), parts(parent(sat), ob))


Tables.getcolumn(row::ACSetRow{T,ob}, i::Int) where {T,ob} =
  Base.getproperty(row, outgoing(parent(row), ob)[i])

Base.getproperty(row::ACSetRow, nm::Symbol) = subpart(parent(row), idx(row), nm)

Tables.getcolumn(row::ACSetRow, nm::Symbol) = Base.getproperty(row, nm)

Base.propertynames(row::ACSetRow{T,ob}) where {T,ob} = outgoing(parent(row), ob)

Tables.columnnames(row::ACSetRow) = Base.propertynames(row)

# ACSet Macro
#############

@ct_enable function _make_acset(@ct(S), T, rows::NamedTuple{names}) where {names}
  @ct begin
    s = SchemaDesc(S)
  end
  acs = T()
  @ct_ctrl for ob in intersect(s.obs, names)
    add_parts!(acs, @ct(ob), rows[@ct ob])
  end
  @ct_ctrl for f in intersect([s.homs; s.attrs], names)
    set_subpart!(acs,:,@ct(f), rows[@ct f])
  end
  acs
end

function make_acset(T::Type{<:StructACSet{S}}, rows::NamedTuple) where {S}
  _make_acset(Val{S}, T, rows)
end

macro acset(head, body)
  tuplized_body = @match body begin
    Expr(:block, lines...) => begin
      params = []
      map(lines) do line
        @match line begin
          Expr(:(=), x, y) => push!(params, Expr(:kw, x, y))
          _ => nothing
        end
      end
      Expr(:tuple, Expr(:parameters, params...))
    end
    _ => error("expected block")
  end
  esc(quote
    $(GlobalRef(CSetDataStructures, :make_acset))($head, $tuplized_body)
  end)
end

# Mapping
#########

function Base.map(acs::ACSet; kwargs...)
  _map(acs, (;kwargs...))
end

function sortunique!(x)
  sort!(x)
  unique!(x)
  x
end

function groupby(f::Function, xs)
  d = Dict{typeof(f(xs[1])),Vector{eltype(xs)}}()
  for x in xs
    k = f(x)
    if k in keys(d)
      push!(d[k],x)
    else
      d[k] = [x]
    end
  end
  d
end

# Eventually should translate this to comptime so it will work with dynamic acsets
@generated function _map(acs::AT, fns::NamedTuple{map_over}) where
  {S, Ts, AT<:StructACSet{S,Ts}, map_over}
  s = SchemaDesc(S)
  map_over = Symbol[map_over...]

  q(s) = Expr(:quote, s)

  mapped_attrs = intersect(s.attrs, map_over)
  mapped_attrtypes = intersect(s.attrtypes, map_over)
  mapped_attrs_from_attrtypes = filter(a -> s.codoms[a] ∈ mapped_attrtypes, s.attrs)
  attrs_accounted_for = sortunique!(Symbol[mapped_attrs; mapped_attrs_from_attrtypes])

  affected_attrtypes = sortunique!(map(a -> s.codoms[a], attrs_accounted_for))
  needed_attrs = sort!(filter(a -> s.codoms[a] ∈ affected_attrtypes, s.attrs))

  unnaccounted_for_attrs = filter(a -> a ∉ attrs_accounted_for, needed_attrs)
  unnaccounted_for_attrs == [] ||
    error("not enough functions provided to fully transform ACSet, need functions for: $(unnaccounted_for_attrs)")

  fn_applications = map(attrs_accounted_for) do a
    qa = q(a)
    if a ∈ mapped_attrs
      :($a = (fns[$qa]).(subpart(acs, $qa)))
    else
      d = s.codoms[a]
      :($a = (fns[$(q(d))]).(subpart(acs, $qa)))
    end
  end

  abc = groupby(a -> s.codoms[a], s.attrs)

  attrtype_instantiations = map(enumerate(s.attrtypes)) do (i,d)
    if d ∈ affected_attrtypes
      :(mapreduce(eltype, typejoin,
                  $(Expr(:tuple, (:(fn_vals[$(q(a))]) for a in abc[d])...))))
    else
      :($(Ts[i]))
    end
  end

  quote
    fn_vals = $(Expr(:tuple, fn_applications...))
    new_acs = $(AT.name.wrapper){$(attrtype_instantiations...)}()
    $(Expr(:block, map(s.obs) do ob
           :(add_parts!(new_acs,$(q(ob)),nparts(acs,$(q(ob)))))
      end...))
    $(Expr(:block, map(s.homs) do hom
           :(set_subpart!(new_acs,$(q(hom)),subpart(acs,$(q(hom)))))
      end...))
    $(Expr(:block, map(s.attrs) do attr
        qa = Expr(:quote, attr)
        if attr ∈ attrs_accounted_for
           :(set_subpart!(new_acs,$qa,fn_vals[$qa]))
        else
           :(set_subpart!(new_acs,$qa,subpart(acs,$qa)))
        end
      end...))
    return new_acs
  end
end

# Presentations
###############

Presentation(::StructACSet{S}) where {S} = Presentation(S)
Presentation(::Type{<:StructACSet{S}}) where {S} = Presentation(S)

end
