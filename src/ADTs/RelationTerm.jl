""" RelationTerm

RelationTerm includes ADT representation of a UWD as well as functions to display UWD
in text format and a constructor to create an ACSet Representation.

"""
module RelationTerm

export Var, Typed, Untyped, Kwarg, Statement, UWDExpr, UWDTerm, context

using MLStyle
using StructTypes
using ..ADTsCore
using ...Programs.RelationalPrograms
using ...WiringDiagrams
using ACSets.ACSetInterface
import Base: show


@data Var <: AbstractTerm begin
 Untyped(var::Symbol)
 Typed(var::Symbol, type::Symbol)
 Kwarg(name::Symbol, var::Var)
end

@doc """   Var

Variables of a UWD. Types are the domain types, ScalarField, VectorField, Dual1Form, Primal2Form NOT Float64,Complex128

Subtypes include:

1. Untyped(var::Symbol)
1. Typed(var::Symbol, type::Symbol)
1. Kwarg(name::Symbol, var::Var)

which are used for representing typed or untyped variables as well as assignment vars.
"""

Var

StructTypes.StructType(::Type{Var}) = StructTypes.AbstractType()
StructTypes.subtypekey(::Type{Var}) = :_type
StructTypes.subtypes(::Type{Var}) = (Untyped=Untyped, Typed=Typed, Kwarg=Kwarg)

@data UWDTerm <: AbstractTerm begin
 Statement(relation::Symbol, variables::Vector{Var})
 UWDExpr(outer_ports::Vector{Var}, context::Vector{Var}, statements::Vector{Statement})
end

@doc """    UWDTerm

Term specifying UWD.

Subtypes
========

1. UWDExpr: A list of outer ports, context of variables, and statements defining a UWD
1. Statement: R(x,y,z) a relation that acts on its arguments (which are Vars)

Example
=======

To specify the following relation macro:
```julia
@relation (x, z) where (x::X, y::Y, z::Z, u::U) begin
  R(x,y)
  S(y,z)
  T(z,y,u)
end
```

Use the following SyntacticModels UWDTerm:

```julia
v1 = Typed(:x, :X)
v2 = Typed(:y, :Y)
v3 = Typed(:z, :Z)
v4 = Untyped(:u)
c = [v1, v2, v3, v4]
op = [v1, v3]
s = [Statement(:R, [v1,v2]),
  Statement(:S, [v2,v3]),
  Statement(:T, [v3,v2, v4])]
u = UWDExpr(op, c, s)
```
"""
UWDTerm

Base.:(==)(s::Statement, t::Statement) = s.relation == t.relation && s.variables == t.variables
Base.:(==)(s::Untyped, t::Untyped) = s.var == t.var
Base.:(==)(s::Typed, t::Typed) = s.var == t.var && s.type == t.type
Base.:(==)(s::Kwarg, t::Kwarg) = s.name == t.name && s.var == t.var

StructTypes.StructType(::Type{UWDTerm}) = StructTypes.AbstractType()
StructTypes.subtypekey(::Type{UWDTerm}) = :_type
StructTypes.subtypes(::Type{UWDTerm}) = (Statement=Statement, UWDExpr=UWDExpr)

varname(v::Var) = @match v begin
  Untyped(v) => v
  Typed(v, t) => v
  Kwarg(n, v) => varname(v)
end

vartype(v::Var) = @match v begin
  Typed(v, t) => t
  Untyped(v) => :untyped
  Kwarg(n, v) => vartype(v)
end

portname(v::Var) = @match v begin
  Kwarg(n, v) => n
  _ => nothing
end

"""    show(io::IO, s::UWDTerm)

generates a human readable string of the `UWDTerm` (or any sub-term).
"""
function show(io::IO, s::UWDTerm)
  let ! = show
    @match s begin
      Statement(r, v) => begin print(io, "$r("); show(io, v, wrap=false); print(io, ")") end
      UWDExpr(op, c, body) => begin
        print(io, op, " ->\n") # Incoporate Better + Add Test, Using for Debugging for now
        map(enumerate(body)) do (i,s)
          if i == 1
            print(io, "{ ")
            show(io, s)
            print(io, "\n")
          elseif i == length(body)
            print(io, "  ")
            show(io, s)
            print(io, " }")
          else
            print(io, "  ")
            show(io, s)
            print(io, "\n")
          end
        end
        print(io, " where ")
        show(io, c)
      end
    end
  end
end

function show(io::IO, c::Vector{Var}; wrap=true)
  # Handling vars:
  show_var(v::Var) = @match v begin
    Untyped(v) => print(io, v)
    Typed(v, T) => print(io, "$v:$T")
    Kwarg(n, v) => begin 
      print(io, "$n=")
      show_var(v)
    end
  end

  if wrap
    print(io, "{")
  end
  map(enumerate(c)) do (i,s)
    show_var(s)
    if i != length(c)
      print(io, ", ")
    end
  end
  if wrap
    print(io, "}")
  end
end

"""    construct(::Type{RelationDiagram}, ex::UWDExpr)

Builds a RelationDiagram from a UWDExpr like the `@relation` macro does for Julia Exprs.
"""
function construct(::Type{RelationDiagram}, ex::UWDExpr)
  # Dealing with Types in Junctions
  var_types = if all(vartype.(ex.context) .== :untyped)
    vars -> length(vars) # Returns count of vars in untyped case
  else
    var_type_map = Dict(zip(varname.(ex.context), vartype.(ex.context))) 
    vars -> getindex.(Ref(var_type_map), varname.(vars)) # Returns list of types in typed Case
  end

  #Dealing with Port names
  port_names(vars::Vector{Var}) = begin
    names = portname.(vars)
    results = @match names begin
      GuardBy(xs -> all(xs .== nothing)) => nothing
      xs => xs
    end
  end

  # Create wiring diagram and add outer ports and junctions
  uwd = RelationDiagram(var_types(ex.outer_ports), port_names=port_names(ex.outer_ports))
  if isempty(ex.context)
    new_vars = unique(ex.outer_ports)
    add_junctions!(uwd, var_types(new_vars), variable=varname.(new_vars))
  else
    add_junctions!(uwd, var_types(ex.context), variable=varname.(ex.context))
  end
  set_junction!(uwd, ports(uwd, outer=true),
                only.(incident(uwd, varname.(ex.outer_ports), :variable)), outer=true)

  # Add box to diagram for each relation call.
  for s in ex.statements 
    box = add_box!(uwd, var_types(s.variables), name=s.relation)
    namedPorts = port_names(s.variables)
    if !isnothing(namedPorts)
      set_subpart!(uwd, ports(uwd, box), :port_name, namedPorts)
    end
    if isempty(ex.context)
      new_vars = setdiff(unique(varname.(s.variables)), uwd[:variable])
      add_junctions!(uwd, var_types(new_vars), variable=new_vars)
    end
    set_junction!(uwd, ports(uwd, box), only.(incident(uwd, varname.(s.variables), :variable)))
  end

  return uwd
end

end