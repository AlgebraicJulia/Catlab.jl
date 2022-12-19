module SparseACSets

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
using ..TypeUtils
using ..LVectors

abstract type SimpleACSet <: ACSet end

""" A `StructACSet` is a SimpleACSet where the schema and the types assigned
to the attrtypes are available in the type.
"""
abstract type StructACSet{S<:TypeLevelSchema{Symbol},Ts<:Tuple} <: SimpleACSet end

""" A special case where there are no attributes.
"""
const StructCSet{S} = StructACSet{S,Tuple{}}

function make_parts(s::Schema{Symbol})
  pi_type(Tuple{Symbol,Type}[(ob, BitSet) for ob in objects(s)])
end

function make_maxes(s::Schema{Symbol})
  LVector{Tuple(objects(s)), Int}
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
  Maxes = make_maxes(s)
  Parts = make_parts(s)
  Subparts = genericize(pi_type(columns), TypeVar[values(Tvars)...])
  quote
    struct $parameterized_type <: $parent{$schema_type, Tuple{$(attrtypes(s)...)}}
      maxes::$Maxes
      parts::$Parts
      subparts::$Subparts
      function $parameterized_type() where {$(attrtypes(s)...)}
        $new_call(
          $Maxes(zeros(Int, $(length(objects(s))))),
          $(pi_type_elt([(ob, :(BitSet())) for ob in objects(s)])),
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
    _ => (head, GlobalRef(SparseACSets, :StructACSet))
  end
  name, schema, idx_args = @match head begin
    Expr(:call, name, schema, idx_args...) => (name, schema, idx_args)
    _ => error("Unsupported head for @acset_type")
  end
  quote
    $(esc(:eval))($(GlobalRef(SparseACSets, :struct_acset))(
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
    _ => (head, GlobalRef(SparseACSets, :StructACSet))
  end
  esc(quote
    abstract type $type{S,Ts} <: $parent{S,Ts} end
  end)
end

@inline ACSetInterface.nparts(acs::SimpleACSet, ob) = length(acs.parts[ob])

@inline ACSetInterface.parts(acs::SimpleACSet, ob) = acs.parts[ob]

@inline _possible_parts(acs::SimpleACSet, ob) = 1:acs.maxes[ob]

@inline function ACSetInterface.add_parts!(acs::SimpleACSet, ob::Symbol, k::Int)
  n = acs.maxes[ob]
  acs.maxes[ob] = n+k
  newparts = (n+1):(n+k)
  union!(acs.parts[ob], newparts)
  newparts
end

@inline default_value(acs::StructACSet{S}, f::Symbol) where {S} = _default_value(Val{S}, Val{f})

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

@inline ACSetInterface.dom_parts(acs::StructACSet{S}, f::Symbol) where {S} = _dom_parts(acs, Val{S}, Val{f})

@ct_enable function _dom_parts(acs, @ct(S), @ct(f))
  @ct s = Schema(S)
  _possible_parts(acs, @ct dom(s, f))
end

@inline ACSetInterface.subpart(acs::SimpleACSet, f::Symbol) =
  view_with_default(acs.subparts[f], dom_parts(acs, f), default_value(acs, f))

@inline ACSetInterface.subpart(acs::SimpleACSet, part::Int, f::Symbol) =
  get(acs.subparts[f], part, default_value(acs, f))

@inline ACSetInterface.set_subpart!(acs::SimpleACSet, i, f, x) =
  acs.subparts[f][i] = x

@inline ACSetInterface.rem_part!(acs::StructACSet{S}, ob, i) where {S} =
  _rem_part!(acs, Val{S}, Val{ob}, i)

@ct_enable function _rem_part!(acs::SimpleACSet, @ct(S), @ct(ob), i)
  delete!(acs.parts[@ct ob], i)
  @ct s = Schema(S)
  @ct outhoms = homs(s; from=ob, just_names=true)
  @ct inhoms = homs(s; from=ob)
  @ct_ctrl for f in outhoms
    delete!(acs.subparts[@ct f], i)
  end
  @ct_ctrl for (f,d,_) in inhoms
    # We could probably do this without a copy, but copy is the simplest way to
    # avoid the problem of mutating while iterating
    to_delete = copy(incident(acs, i, @ct f))
    for j in to_delete
      delete!(acs.subparts[@ct f], j)
    end
  end
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

@ct_enable function _incident(acs::SimpleACSet, @ct(S), ::Colon, @ct(f), unbox_injective)
  @ct s = Schema(S)
  incident(acs, parts(acs, @ct(codom(s, f))), @ct(f); unbox_injective)
end

end
