module TabSet 
export TabularSet

import Tables, PrettyTables

using StructEquality

using GATlab
import GATlab: getvalue

using ..FinSets: ThFinSet
import ..FinSets: FinSet

""" Finite set whose elements are rows of a table.

The underlying table should be compliant with Tables.jl. For the sake of
uniformity, the rows are provided as named tuples, which assumes that the table
is not "extremely wide". This should not be a major limitation in practice but
see the Tables.jl documentation for further discussion.
"""
@struct_hash_equal struct TabularSet
  table::Any
  T::Type
  function TabularSet(table::Any)
    schema = Tables.schema(table)
    new(table, NamedTuple{schema.names, Tuple{schema.types...}})
  end
end

# Accessor
###########

getvalue(t::TabularSet) = t.table

# Other methods 
###############

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

# FinSet Implementation
#######################

@instance ThFinSet{Bool, Any, Int} [model::TabularSet] begin

  in′(i::Any)::Bool = i ∈ getvalue(model)

  eltype()::Any = model.T

  length()::Int = Tables.rowcount(getvalue(model))

  iterate()::Any = 
    iterate(Tables.namedtupleiterator(getvalue(model)))

  iterate(x::Any)::Any = 
    iterate(Tables.namedtupleiterator(getvalue(model)), x)

end

# Default constructor
######################

""" Default kind of FinSet for a `NamedTuple` """
FinSet(nt::NamedTuple) = FinSet(TabularSet(nt))

end # module
