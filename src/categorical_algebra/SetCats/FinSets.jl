""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinSetInt, FinSetHash, TabularSet

using GATlab
import GATlab: getvalue
using StructEquality
using Reexport
import Tables, PrettyTables

using ..Sets, ..SetFunctions
using ..Sets: ThSet′, SetImpl
import ..Sets: SetOb, left, right

import ....Theories: Ob

using ...Cats.Categories: Functor
using ...Cats.FinCats: FinCat, ob_generators

# Theory of FinSets
###################

@theory ThFinSet <: ThSet′ begin
  Int′::TYPE
  length′()::Int′
  iterate′()::Any′
  iterate′(a::Any′)::Any′
end

const M = Model{Tuple{Bool, Any, Int}} # shorthand

abstract type FinSetImpl <: M end 

""" Finite set.

A finite set has abstract type `FinSet{S,T}`. The second type parameter `T` is
the element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type. In
addition, the skeleton of the category **FinSet** is the important special case
`S = Int`. The set ``{1,…,n}`` is represented by the object `FinSet(n)` of type
`FinSet{Int,Int}`.
"""
@struct_hash_equal struct FinSet <: AbsSet
  impl::FinSetImpl
  FinSet(i::FinSetImpl) = implements(i, ThFinSet) ? new(i) : throw(MethodError(
    "Bad model $i"))
end

getvalue(f::FinSet) = f.impl

Base.in(e, f::FinSet) = ThFinSet.in′[getvalue(f)](e)

Base.length(f::FinSet) = ThFinSet.length′[getvalue(f)]()

Base.iterate(f::FinSet, args...) = 
  ThFinSet.iterate′[getvalue(f)](args...)

Base.eltype(s::FinSet) = ThFinSet.eltype′[getvalue(s)]()

# Normally we would have to migrate the model, but because the sorts are the 
# same between the two theories, this is unnecessary.
""" Explicitly cast FinSet as SetOb. This will always succeed. """
# SetOb(f::FinSet) = SetOb(f.impl, getmodel(f)) # migrate_model(ι, f.mod)) 

""" Attempt to cast SetOb to FinSet ... this can throw runtime error."""
# FinSet(s::SetOb) = FinSet(s.impl, s.mod) 

FinSet(set::FinSet) = set

Base.show(io::IO, set::FinSet) = show(io, getvalue(set))
Base.show(io::IO, mime::MIME"text/plain", set::FinSet) = show(io, mime, getvalue(set))
Base.show(io::IO, mime::MIME"text/html", set::FinSet) = show(io, mime, getvalue(set))

# Implementations
#################

# FinSetInt
#---------
"""
A set {1,2,...,n} represented by a single `Int`
"""
@struct_hash_equal struct FinSetInt <: FinSetImpl
  n::Int
end 

getvalue(f::FinSetInt) = f.n

Base.show(io::IO, set::FinSetInt) = print(io, "FinSet($(set.n))")

@instance ThFinSet{Bool, Any, Int} [model::FinSetInt] begin
  in′(i::Any)::Bool = i isa Int && 0 < i ≤ getvalue(model)
  eltype′()::Any = Int
  length′()::Int = getvalue(model)
  iterate′()::Any = iterate(1:getvalue(model))
  iterate′(x::Any)::Any = iterate(1:getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(i::Int) = FinSet(FinSetInt(i))

""" Default FinSet with no parameters """
FinSet() = FinSet(0)

# Ob(C::FinCat{Int}) = FinSet(length(ob_generators(C)))

# FinSetHash
#-----------

"""
A Julia finite set.
"""
@struct_hash_equal struct FinSetHash{T} <: FinSetImpl
  set::Set{T}
end 

getvalue(f::FinSetHash) = f.set

function Base.show(io::IO, set::FinSetHash)
  print(io, "FinSet(")
  show(io, set.set)
  print(io, ")")
end

@instance ThFinSet{Bool, Any, Int} [model::FinSetHash{T}] where T begin
  in′(i::Any)::Bool = i ∈ getvalue(model)
  eltype′() = T
  length′()::Int = length(getvalue(model))
  iterate′()::Any = iterate(getvalue(model))
  iterate′(x::Any)::Any = iterate(getvalue(model), x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s))

# EitherFinSet
#-------------

""" Sum type """
@struct_hash_equal struct EitherFinSet <: FinSetImpl
  left::FinSet
  right::FinSet
end

left(e::EitherFinSet) = e.left
right(e::EitherFinSet) = e.right

@instance ThFinSet{Bool, Any, Int} [model::EitherFinSet] begin
  in′(i::Any)::Bool = i ∈ left(model) || i ∈ right(model)
  eltype′()::Any = Union{eltype(left(model)), eltype(right(model))}
  length′()::Int = length(left(model)) + length(right(model))
  iterate′()::Any = iterate([left(model)...,right(model)...])
  iterate′(x::Any)::Any = iterate([left(model)...,right(model)...], x)
end

""" Default model for a pair of finsets """
FinSet(s::FinSet, r::FinSet) = FinSet(EitherFinSet(s, r))


""" Finite set whose elements are rows of a table.

The underlying table should be compliant with Tables.jl. For the sake of
uniformity, the rows are provided as named tuples, which assumes that the table
is not "extremely wide". This should not be a major limitation in practice but
see the Tables.jl documentation for further discussion.
"""
@struct_hash_equal struct TabularSet <: FinSetImpl
  table::Any
  T::Type
  function TabularSet(table::Any)
    schema = Tables.schema(table)
    new(table, NamedTuple{schema.names, Tuple{schema.types...}})
  end
end

getvalue(t::TabularSet) = t.table

@instance ThFinSet{Bool, Any, Int} [model::TabularSet] begin
  in′(i::Any)::Bool = i ∈ getvalue(model)
  eltype′()::Any = model.T
  length′()::Int = Tables.rowcount(getvalue(model))
  iterate′()::Any = 
    iterate(Tables.namedtupleiterator(getvalue(model)))
  iterate′(x::Any)::Any = 
    iterate(Tables.namedtupleiterator(getvalue(model)), x)
end

function Base.show(io::IO, set::TabularSet)
  print(io, "TabularSet(")
  show(io, set.table)
  print(io, ")")
end

function Base.show(io::IO, ::MIME"text/plain", set::TabularSet)
  print(io, "$(Tables.rowcount(set.table))-element TabularSet")
  if !get(io, :compact, false)
    println(io, ":")
    PrettyTables.pretty_table(io, set.table, show_subheader=false)
  end
end

function Base.show(io::IO, ::MIME"text/html", set::TabularSet)
  println(io, "<div class=\"tabular-set\">")
  println(io, "$(Tables.rowcount(set.table))-element TabularSet")
  PrettyTables.pretty_table(io, set.table, backend=Val(:html), standalone=false,
                            show_subheader=false)
  println(io, "</div>")
end

""" Default kind of FinSet for a `NamedTuple` """
FinSet(nt::NamedTuple) = FinSet(TabularSet(nt))

# FinCat forgetful functor to Set
Ob(C::FinCat{Int}) = FinSet(length(ob_generators(C)))

end # module
