""" 
General utilities for interop between ACSets with Catlab Set+Function 
abstractions, independent of context of any particular category 

TODO this should be written after we have quite a few examples of pointwise 
categories, and then we can know which repeated code makes sense to abstract out
into this file.
"""
module ACSetSetInterop

export sets

using ACSets, CompTime
using ACSets.Columns
using ACSets.DenseACSets: datatypes

import ....BasicSets: SetOb, TypeSet, SetFunction, FinSet, FinFunction, 
                     FinDomFunction
import ...SetCats: VarFunction

""" Create `SetOb` for object or attribute type of attributed C-set.

For objects, the result is a `FinSet`; for attribute types, a `TypeSet`.
"""
@inline SetOb(X::StructACSet{S,Ts}, type::Symbol) where {S,Ts} =
  set_ob(X, Val{S}, Val{Ts}, Val{type})

SetOb(X::DynamicACSet, type::Symbol) =
  runtime(set_ob, X, X.schema, X.type_assignment, type)

@ct_enable function set_ob(X::ACSet, @ct(S), @ct(Ts), @ct(type))
  @ct_ctrl if type ∈ objects(S)
    FinSet(X, @ct type)
  elseif type ∈ attrtypes(S)
    @ct T = attrtype_instantiation(S,Ts,type)
    TypeSet{@ct T}()
  else
    @ct throw(ArgumentError("$(repr(type)) not in $(objects(S)) or $(attrtypes(S))"))
  end
end

""" Create `FinSet` for object of attributed C-set.
"""
@inline FinSet(X::ACSet, type::Symbol) = FinSet(nparts(X, type))

""" Create `TypeSet` for object or attribute type of attributed C-set.
"""
@inline TypeSet(::StructACSet{S,Ts}, type::Symbol) where {S,Ts} =
  type_set(Val{S}, Val{Ts}, Val{type})

TypeSet(X::DynamicACSet, type::Symbol) = 
  runtime(type_set, X.schema, X.type_assignment,type)

@ct_enable function type_set(@ct(S), @ct(Ts), @ct(type))
  @ct begin
    T = if type ∈ objects(S)
      Int
    elseif type ∈ attrtypes(S)
      attrtype_instantiation(S,Ts,type)
    else
      throw(ArgumentError("$(repr(type)) not in $(objects(S)) or $(attrtypes(S))"))
    end
    TypeSet{T}()
  end
end

FinFunction(c::Column{Int,Int}, dom, codom) =
  FinFunction(
    Int[c[i] for i in dom], codom
  )

FinDomFunction(c::Column{Int,Int}, dom, codom)  =
  FinDomFunction([c[i] for i in dom], codom)

"""Runtime error if there are any attributes in the column"""
FinDomFunction(c::Column{Int,Union{AttrVar,T}}, dom, codom) where {T} =
  FinDomFunction(
    T[c[i] for i in dom], codom
  )

function VarFunction(X::ACSet, f::Symbol)
  S = acset_schema(X)
  if f ∈ attrs(S; just_names=true)
    VarFunction(X.subparts[f], parts(X,dom(S,f)), FinSet(nparts(X,codom(S,f))))
  else
    VarFunction(FinFunction(X,f)) #also probably an error
  end
end

VarFunction(c::Column{Int,Union{AttrVar, T}}, dom, codom) where {T} =
  VarFunction{T}([c[i] for i in dom], codom)


""" Create `SetFunction` for morphism or attribute of attributed C-set.

For morphisms, the result is a `FinFunction`; for attributes, a
`FinDomFunction`.
"""
@inline SetFunction(X::StructACSet{S}, name::Symbol) where {S} =
  set_function(X, Val{S}, Val{name})

SetFunction(X::DynamicACSet, name::Symbol)  =
  runtime(set_function,X, acset_schema(X), name)

@ct_enable function set_function(X::SimpleACSet, @ct(S), @ct(name))
  @ct_ctrl if name ∈ objects(S) || name ∈ attrtypes(S)
    SetFunction(identity, SetOb(X, @ct name))
  elseif name ∈ homs(S; just_names=true)
    FinFunction(X.subparts[@ct name], FinSet(X, @ct(dom(S, name))), FinSet(X, @ct(codom(S, name))))
  elseif name ∈ attrs(S; just_names=true)
    FinDomFunction(X, @ct name)
  else
    @ct throw(ArgumentError("$(repr(name)) does not belong to schema $(S)"))
  end
end

""" Create `FinFunction` for morphism of attributed C-set.

Indices are included whenever they exist.
"""
@inline FinFunction(X::StructACSet{S}, name::Symbol) where {S} =
  set_function(X, Val{S}, Val{name})

FinFunction(X::DynamicACSet, name::Symbol)  =
  runtime(set_function,X, acset_schema(X), name)


# WHY DOES THIS EXIST?
""" Create `FinDomFunction` for morphism or attribute of attributed C-set.

Indices are included whenever they exist. Unlike the `FinFunction` constructor,
the codomain of the result is always of type `TypeSet`.
"""
@inline FinDomFunction(X::StructACSet{S}, name::Symbol) where {S} =
  fin_dom_function(X, Val{S}, Val{name})

@ct_enable function fin_dom_function(X::SimpleACSet, @ct(S), @ct(name))
  @ct_ctrl if name ∈ objects(S)
    # n = nparts(X, @ct name)
    # FinDomFunction(1:n, FinSet(n)) # changed from TypeSet
  elseif name ∈ attrs(S; just_names=true) # name ∈ homs(S; just_names=true) || WHY
    FinDomFunction(X.subparts[@ct name], FinSet(X, @ct(dom(S, name))),
                   SetOb(TypeSet(X, @ct(codom(S, name)))))
  else
    @ct throw(ArgumentError("$(repr(name)) not in $(objects(S)), $(homs(S)), or $(attrs(S))"))
  end
end

end # module
