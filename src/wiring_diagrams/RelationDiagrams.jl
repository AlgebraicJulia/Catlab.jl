""" Relation diagrams

This module defines the `RelationDiagram` type, which represents a relation UWD.
"""

module RelationDiagrams

export RelationDiagram, UntypedRelationDiagram, TypedRelationDiagram,
  SchRelationDiagram, SchTypedRelationDiagram,
  SchNamedRelationDiagram, SchTypedNamedRelationDiagram

using GATlab
using ...CategoricalAlgebra.CSets
using ..UndirectedWiringDiagrams

# Data types
############

""" Abstract type for UWDs created by [`@relation`](@ref) macro.
"""
@abstract_acset_type RelationDiagram <: AbstractUWD
@abstract_acset_type _UntypedRelationDiagram <: RelationDiagram
@abstract_acset_type _TypedRelationDiagram <: RelationDiagram

""" Untyped UWD created by [`@relation`](@ref) macro.
"""
const UntypedRelationDiagram{Name,VarName} =
  _UntypedRelationDiagram{S, Tuple{Name,VarName}} where S

""" Typed UWD created by [`@relation`](@ref) macro.
"""
const TypedRelationDiagram{T,Name,VarName} =
  _TypedRelationDiagram{S, Tuple{T,Name,VarName}} where S

@present SchRelationDiagram <: SchUWD begin
  (Name, VarName)::AttrType
  name::Attr(Box, Name)
  variable::Attr(Junction, VarName)
end

@present SchTypedRelationDiagram <: SchTypedUWD begin
  (Name, VarName)::AttrType
  name::Attr(Box, Name)
  variable::Attr(Junction, VarName)
end

@acset_type UntypedUnnamedRelationDiagram(SchRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable]) <: _UntypedRelationDiagram
@acset_type TypedUnnamedRelationDiagram(SchTypedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable]) <: _TypedRelationDiagram

@present SchNamedRelationDiagram <: SchRelationDiagram begin
  port_name::Attr(Port, Name)
  outer_port_name::Attr(OuterPort, Name)
end

@present SchTypedNamedRelationDiagram <: SchTypedRelationDiagram begin
  port_name::Attr(Port, Name)
  outer_port_name::Attr(OuterPort, Name)
end

@acset_type UntypedNamedRelationDiagram(SchNamedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable]) <: _UntypedRelationDiagram
@acset_type TypedNamedRelationDiagram(SchTypedNamedRelationDiagram,
  index=[:box, :junction, :outer_junction], unique_index=[:variable]) <: _TypedRelationDiagram

function UntypedRelationDiagram{Name,VarName}(
    nports::Int; port_names=nothing) where {Name,VarName}
  if isnothing(port_names)
    return UntypedUnnamedRelationDiagram{Name,VarName}(nports)
  end
  d = UntypedNamedRelationDiagram{Name,VarName}(nports)
  set_subpart!(d, :outer_port_name, port_names)
  return d
end

function TypedRelationDiagram{T,Name,VarName}(
    ports::AbstractVector; port_names=nothing) where {T,Name,VarName}
  if isnothing(port_names)
    return TypedUnnamedRelationDiagram{T,Name,VarName}(ports)
  end
  d = TypedNamedRelationDiagram{T,Name,VarName}(ports)
  set_subpart!(d, :outer_port_name, port_names)
  return d
end

RelationDiagram(nports::Int; kw...) =
  UntypedRelationDiagram{Symbol,Symbol}(nports; kw...)
RelationDiagram(ports::AbstractVector{T}; kw...) where T =
  TypedRelationDiagram{T,Symbol,Symbol}(ports; kw...)

end