"""
These are ACSets where the set associated to each object is of the form `1:n`
"""
module DenseACSets
export @acset_type, @abstract_acset_type, @declare_schema, FreeSchema,
  StructACSet, StructCSet, DynamicACSet, SimpleACSet, AnonACSet, StructCSet, ACSetTableType,
  AnonACSetType

using MLStyle
using Reexport
using CompTime
import Tables

@reexport using ..ACSetInterface
@reexport using ..Schemas
using ..Columns
using ..ColumnImplementations
using ..LVectors

# StructACSet Struct Generation
###############################

""" A `SimpleACSet` is an abstract type for any acset that has a certain layout

Specifically, subtypes of `SimpleACSet` are expected to have a `parts` field
which is a mapping from symbols to ints, and a `subparts` field which is a
mapping from symbols to columns, which are any data structure that
satisfies the interface given in Columns.jl.
"""
abstract type SimpleACSet <: ACSet end

""" A `StructACSet` is a SimpleACSet where the schema and the types assigned
to the attrtypes are available in the type.
"""
abstract type StructACSet{S<:TypeLevelSchema{Symbol},Ts<:Tuple} <: SimpleACSet end

""" A special case where there are no attributes.
"""
const StructCSet{S} = StructACSet{S,Tuple{}}

""" Creates a named tuple type
"""
function pi_type(types::Vector{Tuple{Symbol, Type}})
  NamedTuple{Tuple(map(t -> t[1], types)), Tuple{map(t -> t[2], types)...}}
end

""" Creates a quoted element of a named tuple
"""
function pi_type_elt(exprs::Vector{Tuple{Symbol, Expr}})
  Expr(:tuple, Expr(:parameters, [Expr(:kw, f, e) for (f,e) in exprs]...))
end

"""
The type variables that we have generated might not match up with the type
variables that are created as generic parameters to the struct acset, this is a
way of making the two line up
"""
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

function make_parts(s::Schema{Symbol})
  parts_t = LVector{Tuple(objects(s)), Int}
end

function make_columns(s::Schema{Symbol}, index, unique_index, Tvars)
  vcat(
    Tuple{Symbol,Type}[
      (f,column_type(HomChoice, indexchoice(f, index, unique_index)))
      for f in homs(s; just_names=true)
    ],
    Tuple{Symbol,Type}[
      (f,column_type(AttrChoice(Tvars[c]), indexchoice(f, index, unique_index)))
      for (f,_,c) in attrs(s)
    ]
  )
end

""" Create the struct declaration for a `StructACSet` from a Presentation
"""
function struct_acset(name::Symbol, parent, s::Schema{Symbol};
                      index::Vector=[], unique_index::Vector=[])
  Tvars = Dict(at => TypeVar(at) for at in attrtypes(s))
  parameterized_type, new_call = if length(attrtypes(s)) > 0
    (:($name{$(attrtypes(s)...)}), :(new{$(attrtypes(s)...)}))
  else
    name, :new
  end
  schema_type = typelevel(s)
  columns = make_columns(s, index, unique_index, Tvars)
  Parts = make_parts(s)
  Subparts = genericize(pi_type(columns), TypeVar[values(Tvars)...])
  quote
    struct $parameterized_type <: $parent{$schema_type, Tuple{$(attrtypes(s)...)}}
      parts::$Parts
      subparts::$Subparts
      function $parameterized_type() where {$(attrtypes(s)...)}
        $new_call(
          $Parts(zeros(Int, $(length(objects(s))))),
          $(pi_type_elt([(f,:($(genericize(T, TypeVar[values(Tvars)...]))())) for (f,T) in columns]))
        )
      end
      function $parameterized_type(parts::$Parts, subparts::$Subparts) where {$(attrtypes(s)...)}
        $new_call(parts, subparts)
      end
    end
  end
end

unquote(x::QuoteNode) = x.value

""" This macro creates custom structs that subclass `StructACSet{S}` for specific `S`.
These are used for acsets whose schema is known at compile time.
"""
macro acset_type(head)
  head, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(DenseACSets, :StructACSet))
  end
  name, schema, idx_args = @match head begin
    Expr(:call, name, schema, idx_args...) => (name, schema, idx_args)
    _ => error("Unsupported head for @acset_type")
  end
  quote
    $(esc(:eval))($(GlobalRef(DenseACSets, :struct_acset))(
      $(Expr(:quote, name)), $(Expr(:quote, parent)), $(esc(schema));
      $((esc(arg) for arg in idx_args)...)))
    Core.@__doc__ $(esc(name))
  end
end

""" We want control over the type class hierarchy of acsets; this allows us
to create abstract types that subtype StructACSet. For instance, we might have
an `AbstractGraph` type, and then assume (this is not enforced) that any
subtype of `AbstractGraph` has `E,V,src,tgt` in its schema.
"""
macro abstract_acset_type(head)
  type, parent = @match head begin
    Expr(:(<:), h, p) => (h,p)
    _ => (head, GlobalRef(DenseACSets, :StructACSet))
  end
  esc(quote
    abstract type $type{S,Ts} <: $parent{S,Ts} end
  end)
end

""" This is a SimpleACSet which has the schema as a field value rather
than as a type parameter.
"""
struct DynamicACSet <: SimpleACSet
  name::String
  schema::Schema{Symbol}
  type_assignment::Dict{Symbol,Type}
  parts::Dict{Symbol,Int}
  subparts::Dict{Symbol,Column}
  function DynamicACSet(
    name::String,
    s::Schema{Symbol};
    type_assignment=Dict{Symbol,Type}(),
    index::Vector=[],
    unique_index::Vector=[]
  )
    new(
      name,
      s,
      type_assignment,
      Dict(ob => 0 for ob in objects(s)),
      Dict([
        [f => column_type(HomChoice, indexchoice(f,index,unique_index))()
         for f in homs(s; just_names=true)];
        [f => column_type(AttrChoice(type_assignment[c]), indexchoice(f,index,unique_index))()
         for (f,_,c) in attrs(s)]
      ])
    )
  end
  function DynamicACSet(
    name::String,
    schema::Schema{Symbol},
    type_assignment::Dict{Symbol,Type},
    parts::Dict{Symbol,Int},
    subparts::Dict{Symbol,Column}
  )
    new(name,schema,type_assignment,parts,subparts)
  end
end

""" This works the same as something made with `@acset_type`, only the types of the
parts and subparts are stored as type parameters. Thus, this can be used with any schema.
"""
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
      Parts(zeros(Int64, length(S.parameters[2].parameters))),
      Subparts(T() for T in Subparts.parameters[2].parameters)
    )
  end

  function AnonACSet(
    s::Schema{Symbol};
    type_assignment=Dict{Symbol,Type}(),
    index::Vector{Symbol}=Symbol[],
    unique_index::Vector{Symbol}=Symbol[]
  )
    T = AnonACSetType(s; type_assignment, index=index, unique_index=unique_index)
    T()
  end
end

""" This can be used to fill out the type parameters to an AnonACSet ahead of time.
"""
function AnonACSetType(
  s::Schema;
  type_assignment::Dict{Symbol, Type}=Dict{Symbol,Type}(),
  index::Vector=[],
  unique_index::Vector=[],
  union_all::Bool=false
)
  (!union_all || isempty(type_assignment)) || error("If union_all is true, then attrtypes must be empty")
  S = typelevel(s)
  if union_all
    Tvars = Dict(at => TypeVar(at) for at in attrtypes(s))
  else
    Tvars = type_assignment
  end
  Ts = Tuple{(Tvars[at] for at in attrtypes(s))...}
  columns = make_columns(s, index, unique_index, Tvars)
  Parts = make_parts(s)
  Subparts = pi_type(columns)
  T = AnonACSet{S,Ts,Parts,Subparts}
  if union_all
    foldr(UnionAll, [Tvars[at] for at in attrtypes(s)]; init=T)
  else
    T
  end
end

function ACSetTableSchema(s::Schema{Symbol}, ob::Symbol)
  attrs = filter(Schemas.attrs(s)) do (f,d,c)
    d == ob
  end
  BasicSchema{Symbol}([ob], [], attrtypes(s), attrs)
end

function ACSetTableDataType(::Type{<:StructACSet{S,Ts}}, ob::Symbol) where {S,Ts}
  s = Schema(S)
  s′ = ACSetTableSchema(s,ob)
  type_assignment = Dict{Symbol, Type}(a => T for (a,T) in zip(attrtypes(s), Ts.parameters))
  AnonACSetType(s′; type_assignment)
end

function ACSetTableUnionAll(::Type{<:StructACSet{S}}, ob::Symbol) where {S}
  s′ = ACSetTableSchema(Schema(S),ob)
  AnonACSetType(s′;union_all=true)
end

""" This takes an ACSet type, and produces an AnonACSet which represents an
acset with just the object passed in, and then all of the attributes of that
object.

TODO: rename this to be less confusing with ACSetTable. Maybe ASet (attributed
set)
"""
function ACSetTableType(X::Type, ob::Symbol; union_all::Bool=false)
  (union_all ? ACSetTableUnionAll : ACSetTableDataType)(X, ob)
end

Base.copy(acs::DynamicACSet) =
  DynamicACSet(
    acs.name,
    acs.schema,
    acs.type_assignment,
    copy(acs.parts),
    deepcopy(acs.subparts)
  )

Base.copy(acs::T) where {T <: StructACSet} = T(copy(acs.parts), map(copy, acs.subparts))

Base.:(==)(acs1::T, acs2::T) where {T <: SimpleACSet} =
  acs1.parts == acs2.parts && acs1.subparts == acs2.subparts

ACSetInterface.acset_schema(acs::StructACSet{S}) where {S} = Schema(S)
ACSetInterface.acset_schema(acs::DynamicACSet) = acs.schema

add_parts_with_indices!(acs::SimpleACSet, ob::Symbol, n::Int, index_sizes::NamedTuple) =
  add_parts!(acs, ob, n)

Base.hash(x::T, h::UInt) where T <: SimpleACSet =
  hash(x.parts, hash(x.subparts, h))

@inline function ACSetInterface.add_parts!(acs::SimpleACSet, ob::Symbol, n::Int)
  m = acs.parts[ob]
  nparts = m + n
  newparts = (m+1):nparts
  acs.parts[ob] = nparts
  newparts
end

@inline ACSetInterface.nparts(acs::SimpleACSet, type::Symbol) = acs.parts[type]

ACSetInterface.has_part(acs::StructACSet{S}, ob::Symbol) where {S} =
  _has_part(Val{S}, Val{ob})

ACSetInterface.has_part(acs::DynamicACSet, ob::Symbol) =
  runtime(_has_part, acs.schema, ob)

@ct_enable function _has_part(@ct(S), @ct(ob))
  @ct s = Schema(S)
  @ct ob ∈ objects(s)
end

outgoing(acs::StructACSet{S}, ob::Symbol) where {S} = _outgoing(Val{S}, Val{ob})

outgoing(acs::DynamicACSet, ob::Symbol) = runtime(_outgoing, acs.schema, ob)

@ct_enable function _outgoing(@ct(S), @ct(ob))
  @ct s = Schema(S)
  @ct Tuple(arrows(s; from=ob, just_names=true))
end

@inline default_value(acs::StructACSet{S}, f::Symbol) where {S} = _default_value(Val{S}, Val{f})
@inline default_value(acs::DynamicACSet, f::Symbol) = runtime(_default_value, acs.schema, f)

@ct_enable function _default_value(@ct(S), @ct(f))
  @ct begin
    s = Schema(S)
    if f ∈ homs(s; just_names=true)
      0
    elseif f ∈ attrs(s; just_names=true)
      nothing
    else
      error("$f not in schema")
    end
  end
end

@inline ACSetInterface.subpart(acs::SimpleACSet, f::Symbol) =
  view_with_default(acs.subparts[f], dom_parts(acs, f), default_value(acs, f))

@inline ACSetInterface.subpart(acs::SimpleACSet, part::Int, f::Symbol) =
  get(acs.subparts[f], part, default_value(acs, f))

@inline ACSetInterface.has_subpart(acs::StructACSet{S}, f::Symbol) where {S} =
  _has_subpart(Val{S}, Val{f})

ACSetInterface.has_subpart(acs::DynamicACSet, f::Symbol) =
  runtime(_has_subpart, acs.schema, f)

@ct_enable function _has_subpart(@ct(S), @ct(f))
  @ct s = Schema(S)
  @ct f ∈ arrows(s; just_names=true)
end

@inline ACSetInterface.dom_parts(acs::StructACSet{S}, f::Symbol) where {S} = _dom_parts(acs, Val{S}, Val{f})
@inline ACSetInterface.dom_parts(acs::DynamicACSet, f::Symbol) = runtime(_dom_parts, acs, acs.schema, f)

@ct_enable function _dom_parts(acs, @ct(S), @ct(f))
  @ct s = Schema(S)
  parts(acs, @ct dom(s, f))
end

@inline ACSetInterface.incident(acs::SimpleACSet, part, f::Symbol; unbox_injective=true) =
  if !unbox_injective
    preimage(dom_parts(acs, f), acs.subparts[f], part)
  else
    preimage(dom_parts(acs, f), acs.subparts[f], part, UnboxInjectiveFlag())
  end

@inline ACSetInterface.incident(acs::SimpleACSet, parts::Union{AbstractVector,UnitRange}, f::Symbol; unbox_injective=true) =
  if !unbox_injective
    preimage_multi(dom_parts(acs, f), acs.subparts[f], parts)
  else
    preimage_multi(dom_parts(acs, f), acs.subparts[f], parts, UnboxInjectiveFlag())
  end

@inline ACSetInterface.incident(acs::StructACSet{S}, ::Colon, f::Symbol; unbox_injective=true) where {S} =
  _incident(acs, Val{S}, :, Val{f}, unbox_injective)

ACSetInterface.incident(acs::DynamicACSet, ::Colon, f::Symbol; unbox_injective=true) =
  runtime(_incident, acs, acs.schema, :, f, unbox_injective)

@ct_enable function _incident(acs::SimpleACSet, @ct(S), ::Colon, @ct(f), unbox_injective)
  @ct s = Schema(S)
  incident(acs, parts(acs, @ct(codom(s, f))), @ct(f); unbox_injective)
end

@inline ACSetInterface.set_subpart!(acs::StructACSet{S}, part::Int, f::Symbol, subpart) where {S} =
  _set_subpart!(acs, Val{S}, part, Val{f}, subpart)

ACSetInterface.set_subpart!(acs::DynamicACSet, part::Int, f::Symbol, subpart) =
  runtime(_set_subpart!, acs, acs.schema, part, f, subpart)

@ct_enable function _set_subpart!(acs::SimpleACSet, @ct(S), part, @ct(f), subpart)
  @ct s = Schema(S)
  @ct_ctrl if f ∈ homs(s; just_names=true)
    @assert 0 <= subpart <= acs.parts[@ct codom(s, f)]
  end
  acs.subparts[@ct f][part] = subpart
end

@inline ACSetInterface.clear_subpart!(acs::SimpleACSet, part::Int, f::Symbol) =
  delete!(acs.subparts[f], part)

@inline ACSetInterface.rem_part!(acs::StructACSet{S}, type::Symbol, part::Int) where {S} =
  _rem_part!(acs, Val{S}, Val{type}, part)

ACSetInterface.rem_part!(acs::DynamicACSet, type::Symbol, part::Int) =
  runtime(_rem_part!, acs, acs.schema, type, part)

@ct_enable function _rem_part!(acs::SimpleACSet, @ct(S), @ct(ob), part)
  @ct s = Schema(S)
  @ct in_homs = homs(s; to=ob, just_names=true)
  @ct out_homs = homs(s; from=ob, just_names=true)
  @ct out_attrs = attrs(s; from=ob, just_names=true)

  last_part = acs.parts[@ct ob]

  @ct_ctrl for hom in in_homs
    incoming_to_part = copy(incident(acs, part, @ct hom; unbox_injective=false))
    clear_subpart!(acs, incoming_to_part, @ct hom)

    incoming_to_last_part = copy(incident(acs, last_part, @ct hom; unbox_injective=false))
    set_subpart!(acs, incoming_to_last_part, (@ct hom), part)
  end

  @ct_ctrl for f in [out_homs; out_attrs]
    if haskey(acs.subparts[@ct f], last_part)
      set_subpart!(acs, part, (@ct f), subpart(acs, last_part, @ct f))
    end
    clear_subpart!(acs, last_part, @ct f)
  end

  acs.parts[@ct ob] -= 1
end

# Copy Parts
############

@ct_enable function common_objects(@ct(S), @ct(S′))
  @ct s,s′ = Schema(S), Schema(S′)
  @ct Tuple(intersect(objects(s), s′.obs))
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
    s, s′ = Schema(S), Schema(S′)
    @assert obs ⊆ intersect(objects(s), objects(s′))
    common_homs = intersect(homs(s), homs(s′))
    relevant_homs = [(f,d,c) for (f,d,c) in common_homs if d ∈ obs && c ∈ obs]
    in_obs = unique!([c for (_,_,c) in relevant_homs])
  end

  newparts = copy_parts_only!(to, from, parts)
  partmaps = NamedTuple{@ct Tuple(in_obs)}(((@ct_ctrl (
    Dict{Int,Int}(zip(parts[@ct type], newparts[@ct type]))
    for type in in_obs
  )...),))

  @ct_ctrl for (f, d, c) in relevant_homs
    for (p, newp) in zip(parts[@ct d], newparts[@ct d])
      q = subpart(from, p, @ct f)
      newq = get(partmaps[@ct c], q, nothing)
      if !isnothing(newq)
        set_subpart!(to, newp, @ct(f), newq)
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
    s, s′ = Schema(S), Schema(S′)
    @assert obs ⊆ intersect(objects(s), objects(s′))
    common_attrs = intersect(attrs(s), attrs(s′))
    relevant_attrs = [(f,d,c) for (f,d,c) in common_attrs if d ∈ obs]
  end

  newparts = NamedTuple{@ct obs}((@ct_ctrl(
    (add_parts!(to, @ct(ob), length(parts[@ct ob])) for ob in obs)...
  ),))

  @ct_ctrl for (a,d,c) in relevant_attrs
    set_subpart!(to, newparts[@ct d], @ct(a), subpart(from, parts[@ct d], @ct(a)))
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
  if length(attrtypes(s)) == 0
    x.name
  else
    Ts = join([x.type_assignment[at] for at in attrtypes(s)], ",")
    "$(x.name){$(Ts)}"
  end
end

function Base.show(io::IO, acs::SimpleACSet)
  s = acset_schema(acs)
  if get(io, :compact, false)
    print(io, acset_name(acs))
    print(io, " {")
    join(io, ("$ob = $(nparts(acs,ob))" for ob in objects(s)), ", ")
    print(io, "}")
  else
    print(io, acset_name(acs))
    println(io, ":")
    join(io, Iterators.flatten((
      ("  $ob = $(parts(acs,ob))" for ob in objects(s)),
      ("  $f : $d → $c = $(subpart(acs,f))"
       for (f,d,c) in homs(s)),
      ("  $a : $d → $c = $(subpart(acs,a))"
       for (a,d,c) in attrs(s)),
    )), "\n")
  end
end

# Tables
########

struct ACSetTable{T<:ACSet, ob} <: Tables.AbstractColumns
  parent::T
end

ACSetTable(acs::ACSet, ob::Symbol) = ACSetTable{typeof(acs), ob}(acs)

ACSetInterface.tables(acs::StructACSet{<:TypeLevelBasicSchema{Name, obs}}) where {Name, obs} =
  NamedTuple([ob => ACSetTable(acs, ob) for ob in obs.parameters])

ACSetInterface.tables(acs::DynamicACSet) =
  NamedTuple([ob => ACSetTable(acs, ob) for ob in objects(acs.schema)])

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
    s = Schema(S)
  end
  acs = T()
  @ct_ctrl for ob in intersect(objects(s), names)
    add_parts!(acs, @ct(ob), rows[@ct ob])
  end
  @ct_ctrl for f in intersect(arrows(s; just_names=true), names)
    set_subpart!(acs, :, @ct(f), rows[@ct f])
  end
  acs
end

function make_acset(T::Type{<:StructACSet{S}}, rows::NamedTuple) where {S}
  _make_acset(Val{S}, T, rows)
end

"""
This provides a shorthand for constructing an acset by giving its parts and
subparts

Usage:

@acset WeightedGraph{String} begin
  V = 2
  E = 1
  src = [1]
  tgt = [2]
  weight = ["fig"]
end
"""
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
    $(GlobalRef(DenseACSets, :make_acset))($head, $tuplized_body)
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
  s = Schema(S)
  map_over = Symbol[map_over...]

  q(s) = Expr(:quote, s)

  mapped_attrs = intersect(attrs(s; just_names=true), map_over)
  mapped_attrtypes = intersect(attrtypes(s), map_over)
  mapped_attrs_from_attrtypes = [a for (a,d,c) in attrs(s) if c ∈ mapped_attrtypes]
  attrs_accounted_for = sortunique!(Symbol[mapped_attrs; mapped_attrs_from_attrtypes])

  affected_attrtypes = sortunique!(map(a -> codom(s,a), attrs_accounted_for))
  needed_attrs = sort!([a for (a,d,c) in attrs(s) if c ∈ affected_attrtypes])

  unnaccounted_for_attrs = filter(a -> a ∉ attrs_accounted_for, needed_attrs)
  unnaccounted_for_attrs == [] ||
    error("not enough functions provided to fully transform ACSet, need functions for: $(unnaccounted_for_attrs)")

  fn_applications = map(attrs_accounted_for) do a
    qa = q(a)
    if a ∈ mapped_attrs
      :($a = (fns[$qa]).(subpart(acs, $qa)))
    else
      d = codom(s,a)
      :($a = (fns[$(q(d))]).(subpart(acs, $qa)))
    end
  end

  abc = groupby(a -> codom(s,a), attrs(s; just_names=true))

  attrtype_instantiations = map(enumerate(attrtypes(s))) do (i,d)
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
    $(Expr(:block, map(objects(s)) do ob
           :(add_parts!(new_acs,$(q(ob)),nparts(acs,$(q(ob)))))
      end...))
    $(Expr(:block, map(homs(s; just_names=true)) do f
           :(set_subpart!(new_acs,$(q(f)),subpart(acs,$(q(f)))))
      end...))
    $(Expr(:block, map(attrs(s; just_names=true)) do a
        qa = Expr(:quote, a)
        if a ∈ attrs_accounted_for
           :(set_subpart!(new_acs,$qa,fn_vals[$qa]))
        else
           :(set_subpart!(new_acs,$qa,subpart(acs,$qa)))
        end
      end...))
    return new_acs
  end
end

end
