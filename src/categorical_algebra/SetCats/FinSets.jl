""" The category of finite sets and functions, and its skeleton.
"""
module FinSets
export FinSet, FinSetInt, FinSetHash, TabularSet

using GATlab
using StructEquality
using Reexport
import Tables, PrettyTables

using ..Sets, ..SetFunctions
using ..Sets: ThSet′, M, SetImpl
import ..Sets: getmodel, SetOb

import ....Theories: Ob

# using ..FinCats: FinCat, ob_generators

# Theory of FinSets
###################

@theory ThFinSet <: ThSet′ begin
  length′(s::Set′)::Int′
  iterate′(s::Set′)::Any′
  iterate′(s::Set′,a::Any′)::Any′
end

abstract type FinSetImpl <: SetImpl end 

""" Finite set.

A finite set has abstract type `FinSet{S,T}`. The second type parameter `T` is
the element type of the set and the first parameter `S` is the collection type,
which can be a subtype of `AbstractSet` or another Julia collection type. In
addition, the skeleton of the category **FinSet** is the important special case
`S = Int`. The set ``{1,…,n}`` is represented by the object `FinSet(n)` of type
`FinSet{Int,Int}`.
"""
@struct_hash_equal struct FinSet <: AbsSet
  impl::Any
  mod::Any
  FinSet(i::T, m::M{T}) where {T<:FinSetImpl} = 
    implements(m, ThFinSet) ? new(i, m) : throw(MethodError("Bad model $i $m"))
end

GATlab.getvalue(f::FinSet) = f.impl

getmodel(f::FinSet) = f.mod

Base.in(e, f::FinSet) = ThFinSet.in′[getmodel(f)](e, getvalue(f))

Base.length(f::FinSet) = ThFinSet.length′[getmodel(f)](getvalue(f))

Base.iterate(f::FinSet, args...) = 
  ThFinSet.iterate′[getmodel(f)](getvalue(f), args...)

Base.eltype(s::FinSet) = ThFinSet.eltype′[getmodel(s)](getvalue(s))

# Normally we would have to migrate the model, but because the sorts are the 
# same between the two theories, this is unnecessary.
""" Explicitly cast FinSet as SetOb. This will always succeed. """
SetOb(f::FinSet) = SetOb(f.impl, getmodel(f)) # migrate_model(ι, f.mod)) 

""" Attempt to cast SetOb to FinSet ... this can throw runtime error."""
FinSet(s::SetOb) = FinSet(s.impl, s.mod) 

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

Base.show(io::IO, set::FinSetInt) = print(io, "FinSet($(set.n))")

@struct_hash_equal struct FinSetIntImpl <: M{FinSetInt} end

@instance ThFinSet{Bool, Int, Any, FinSetInt} [model::FinSetIntImpl] begin
  in′(i::Any, s::FinSetInt)::Bool = i isa Int && 0 < i ≤ s.n
  eltype′(s::FinSetInt)::Any = Int
  length′(s::FinSetInt)::Int = s.n
  iterate′(s::FinSetInt)::Any = iterate(1:s.n)
  iterate′(s::FinSetInt, x::Any)::Any = iterate(1:s.n, x)
end

""" Default `ThFinSet` model for a FinSetInt` """
FinSet(i::FinSetInt) = FinSet(i, FinSetIntImpl())

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

GATlab.getvalue(f::FinSetHash) = f.set

function Base.show(io::IO, set::FinSetHash)
  print(io, "FinSet(")
  show(io, set.set)
  print(io, ")")
end

@struct_hash_equal struct FinSetHashImpl{T} <: M{FinSetHash{T}} end

@instance ThFinSet{Bool, Int, Any, FinSetHash{T}
                  } [model::FinSetHashImpl{T}] where T begin
  in′(i::Any, s::FinSetHash{T})::Bool = i ∈ s.set
  eltype′(s::FinSetHash{T}) = T
  length′(s::FinSetHash{T})::Int = length(s.set)
  iterate′(s::FinSetHash{T})::Any = iterate(s.set)
  iterate′(s::FinSetHash{T}, x::Any)::Any = iterate(s.set, x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s), FinSetHashImpl{T}())

# EitherFinSet
#-------------

""" Sum type """
@struct_hash_equal struct EitherFinSet <: FinSetImpl
  left::FinSet
  right::FinSet
end

@struct_hash_equal struct EitherFinSetImpl  <: M{EitherFinSet} end

@instance ThFinSet{Bool, Int, Any, EitherFinSet} [model::EitherFinSetImpl] begin
  in′(i::Any, s::EitherFinSet)::Bool = i ∈ s.left || i ∈ s.right
  eltype′(f::EitherFinSet)::Any = Union{eltype(s.left), eltype(s.right)}
  length′(s::EitherFinSet)::Int = length(s.left) + length(s.right)
  iterate′(s::EitherFinSet)::Any = iterate([s.left...,s.right...])
  iterate′(s::EitherFinSet, x::Any)::Any = iterate([s.left...,s.right...], x)
end

""" Default model for an eitherset """
FinSet(s::EitherFinSet) = FinSet(s, EitherFinSetImpl())


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

GATlab.getvalue(t::TabularSet) = t.table

@struct_hash_equal struct TabularSetImpl  <: M{TabularSet} end

@instance ThFinSet{Bool, Int, Any, TabularSet} [model::TabularSetImpl] begin
  in′(i::Any, s::TabularSet)::Bool = i ∈ getvalue(s)
  eltype′(f::TabularSet)::Any = f.T
  length′(s::TabularSet)::Int = Tables.rowcount(s.table)
  iterate′(s::TabularSet)::Any = 
    iterate(Tables.namedtupleiterator(getvalue(s)))
  iterate′(s::TabularSet, x::Any)::Any = 
    iterate(Tables.namedtupleiterator(getvalue(s)), x)
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
FinSet(nt::NamedTuple) = FinSet(TabularSet(nt), TabularSetImpl())


end # module
