""" RelationTerm

RelationTerm includes ADT representation of a UWD as well as functions to display UWD
in text format and a constructor to create an ACSet Representation.

"""
module RelationTerm

export Var, Typed, Untyped, Statement, UWDExpr, UWDTerm, context

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
end

@doc """   Var

Variables of a UWD. Types are the domain types, ScalarField, VectorField, Dual1Form, Primal2Form NOT Float64,Complex128

Subtypes include:

1. Untyped(var::Symbol)
1. Typed(var::Symbol, type::Symbol)

which are used for representing typed or untyped variables.
"""

Var

StructTypes.StructType(::Type{Var}) = StructTypes.AbstractType()
StructTypes.subtypekey(::Type{Var}) = :_type
StructTypes.subtypes(::Type{Var}) = (Untyped=Untyped, Typed=Typed)

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

StructTypes.StructType(::Type{UWDTerm}) = StructTypes.AbstractType()
StructTypes.subtypekey(::Type{UWDTerm}) = :_type
StructTypes.subtypes(::Type{UWDTerm}) = (Statement=Statement, UWDExpr=UWDExpr)

varname(v::Var) = @match v begin
  Untyped(v) => v
  Typed(v, t) => v
end

vartype(v::Var) = @match v begin
  Typed(v, t) => t
  Untyped(v) => :untyped # Maybe want to output nothing stored if it is untyped
end

context(t::UWDTerm) = @match t begin
  Statement(R, xs) => xs
  UWDExpr(outer_ports, context, statements) => context
end

outer_ports(t::UWDTerm) = @match t begin
  UWDExpr(outer_ports, context, statements) => outer_ports
  _ => nothing # Not sure if this is the ideal way.
end

"""    show(io::IO, s::UWDTerm)

generates a human readable string of the `UWDTerm` (or any sub-term).
"""
function show(io::IO, s::UWDTerm)
  let ! = show
    @match s begin
      Statement(r, v) => begin print(io, "$r("); show(io, v, wrap=false); print(io, ")") end
      UWDExpr(op, c, body) => begin 
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
  if wrap
    print(io, "{")
  end
  map(enumerate(c)) do (i,s)
    @match s begin
      Untyped(v) => print(io, v)
      Typed(v, T) => print(io, "$v:$T")
    end
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

  # Create wiring diagram and add outer ports and junctions
  uwd = RelationDiagram(var_types(ex.outer_ports))
  if isnothing(ex.context)
    new_vars = unique(ex.outer_ports)
    add_junctions!(uwd, var_types(new_vars), variable=varname.(new_vars))
  else
    add_junctions!(uwd, var_types(ex.context), variable=varname.(ex.context))
  end
  set_junction!(uwd, ports(uwd, outer=true),
                only.(incident(uwd, varname.(ex.outer_ports), :variable)), outer=true)


  # uwd = RelationDiagram(map(varname, ex.context))

  # add_parts!(uwd, :Junction, length(ex.context), variable=varname.(ex.context), junction_type=vartype.(ex.context))
  # junctions = uwd[:, :variable]
  
  # junction(name) = only(incident(uwd, :varname, name))
  # for var in ex.outer_ports
  #   try k = junction(varname(a))
  #     op_id = add_part!(uwd, :OuterPorts, outer_junction=k)
  #   catch
  #     k = add_part!(uwd, :Junction, variable=varname(a), junction_type=vartype(a))    
  #     op_id = add_part!(uwd, :OuterPorts, outer_junction=k)
  #   end
  # end
  
  # # then for each statement we add a box, and its ports
  # for s in ex.statements
  #   b = add_part!(uwd, :Box, name=s.relation)
  #   for a in s.variables
  #     # if a junction is missing, we have to add it. This is for implicit variables that weren't in the context
  #     try k = junction(varname(a))
  #       # every port connects to the junction with the same variable name
  #       add_part!(uwd, :Port, box=b, port_type=vartype(a), junction=junction(varname(a)))
  #     catch
  #       k = add_part!(uwd, :Junction, variable=varname(a), junction_type=vartype(a))    
  #       add_part!(uwd, :Port, box=b, port_type=vartype(a), junction=junction(varname(a)))
  #     end
  #   end
  # end
  # return uwd
end

end