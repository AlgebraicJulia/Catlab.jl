module TabularSets 
export TabularSet

using StructEquality
import Tables, PrettyTables

using ..FinSets 
import ..FinSets: FinSet

""" Finite set whose elements are rows of a table.

The underlying table should be compliant with Tables.jl. For the sake of
uniformity, the rows are provided as named tuples, which assumes that the table
is not "extremely wide". This should not be a major limitation in practice but
see the Tables.jl documentation for further discussion.
"""
@struct_hash_equal struct TabularSet{Table,Row} <: FinSet{Table,Row}
  table::Table

  function TabularSet(table::Table) where Table
    schema = Tables.schema(table)
    new{Table,NamedTuple{schema.names,Tuple{schema.types...}}}(table)
  end
end

FinSet(nt::NamedTuple) = TabularSet(nt)

Base.iterate(set::TabularSet, args...) =
  iterate(Tables.namedtupleiterator(set.table), args...)
Base.length(set::TabularSet) = Tables.rowcount(set.table)
Base.collect(set::TabularSet) = Tables.rowtable(set.table)

function Base.show(io::IO, set::TabularSet)
  print(io, "TabularSet(")
  show(io, set.table)
  print(io, ")")
end

function Base.show(io::IO, ::MIME"text/plain", set::TabularSet{T}) where T
  print(io, "$(length(set))-element TabularSet{$T}")
  if !get(io, :compact, false)
    println(io, ":")
    PrettyTables.pretty_table(io, set.table, show_subheader=false)
  end
end

function Base.show(io::IO, ::MIME"text/html", set::TabularSet)
  println(io, "<div class=\"tabular-set\">")
  println(io, "$(length(set))-element TabularSet")
  PrettyTables.pretty_table(io, set.table, backend=Val(:html), standalone=false,
                            show_subheader=false)
  println(io, "</div>")
end

end # module