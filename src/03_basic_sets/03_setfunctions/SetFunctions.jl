export SetFunction, ThSetFunction

using StructEquality

using GATlab

import ....Theories: dom, codom
using ..Sets
using ..FinSets: FinSet, FinSetInt

# Theory of SetFunctions
########################

"""
Interface we require any implementation of `SetFunction` to satisfy. We should 
be able to extract a (co)dom, apply the function to inputs, and postcompose.

Often, implementations are naturally postcomposed with another function, because 
this allows one to keep the same structure but just update the values. However,
there are _some_ function implementations which do fundamentally change upon 
postcomposition, such as an `IdentityFunction`. Also, in the case of  
`ConstantFunction`s, one more efficiently represents a postcomposition not by 
mapping over the structure with the same value but by just replacing the
function with another `ConstantFunction`. `postcompose` is only ever called when
using `force` to evaluate a `CompositeFunction`.
"""
@theory ThSetFunction begin
  Any′::TYPE
  Fun′::TYPE
  DomSet::TYPE
  CodSet::TYPE
  dom()::DomSet
  codom()::CodSet
  app(e::Any′)::Any′
  postcompose(t::Fun′)::Fun′
end

# Wrapper type for models of ThSetFunction
##########################################

""" Generic type for morphism in the category **Set**.

Note: This type would be better called simply `Function` but that name is
already taken by the base Julia type.
"""
ThSetFunction.Meta.@typed_wrapper SetFunction

SetFunction(s::SetFunction) = s

(f::SetFunction)(x) = ThSetFunction.app(f, x)

Base.show(io::IO, f::SetFunction) = show(io, getvalue(f)) 

function show_domains(io::IO, f::SetFunction; domain::Bool=true, 
    codomain::Bool=true, recurse::Bool=true)
  get(io, :hide_domains, false) && return print(io, "…")
  domain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
  domain && codomain && print(io, ", ")
  codomain && show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
end

