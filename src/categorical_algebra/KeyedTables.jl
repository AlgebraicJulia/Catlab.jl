""" This module provides a type KeyedTable, which sports a Tables.jl-compatible
interface where rows of the table can be indexed by elements of an arbitrary type,
not just elements of the range 1:n
"""

module KeyedTables

export KeyedTable, key, index, setkey

using Tables

"""This is a table where each row can have an optional associated key.

The parameters are KT (Key Type) and TT (Table Type)
"""
struct KeyedTable{KT, TT}
  table::TT
  keys::Vector{Union{KT,Nothing}}
  index::Dict{KT,Int64}
  function KeyedTable{KT}(table::TT) where {KT,TT}
    new{KT,TT}(table,fill(nothing,length(table)),Dict{KT,Int64}())
  end
  KeyedTable(table::TT, keys::Vector{KT}) where {KT,TT} =
    KeyedTable(table,convert(Vector{Union{KT,Nothing}},keys))
  function KeyedTable(table::TT,keys::Vector{Union{KT,Nothing}}) where {KT,TT}
    @assert length(table) == length(keys)
    index = Dict{KT,Int64}()
    for (i,x) in enumerate(keys)
      if x != nothing
        index[x] = i
      end
    end
    new{KT,TT}(table,keys,index)
  end
  function KeyedTable{KT, TT}() where {KT,TT}
    KeyedTable{KT}(TT())
  end
end

_table(kt::KeyedTable) = getfield(kt,:table)
_keys(kt::KeyedTable) = getfield(kt,:keys)
_index(kt::KeyedTable) = getfield(kt,:index)

getproperty(kt::KeyedTable,prop::Symbol) = getproperty(_table(kt),prop)

Tables.istable(kt::KeyedTable) = Tables.rowaccess(_table(kt))

Tables.rowaccess(kt::KeyedTable) = Tables.rowaccess(_table(kt))

Tables.rows(kt::KeyedTable) = kt

Tables.columnaccess(kt::KeyedTable) = false

Tables.getcolumn(kt::KeyedTable,i::Int) = Tables.getcolumn(Tables.rows(_table(kt)),i)

Tables.getcolumn(kt::KeyedTable,nm::Symbol) = Tables.getcolumn(Tables.rows(_table(kt)),nm)

Tables.columnnames(kt::KeyedTable) = Tables.columnnames(_table(kt))

Tables.getcolumn(kt::KeyedTable,::Type{T}, i::Int, nm::Symbol) where {T} =
  Tables.getcolumn(Tables.rows(_table(kt)), T, i, nm)

Tables.isrowtable(kt::KeyedTable) = true

function Tables.getcolumn(kt::KeyedTable{KT}, ::Type{T}, i::KT, nm::Symbol) where {T,KT}
  Tables.getcolumn(kt, T, _index(kt)[i], nm)
end

function Base.push!(kt::KeyedTable{KT}, row, key::Union{Nothing,KT}=nothing) where {KT}
  i = length(_table(kt)) + 1
  if key != nothing
    @assert !(key in keys(kt))
    _index(kt)[key] = i
  end
  push!(_table(kt),row)
  push!(_keys(kt),key)
end

function Base.append!(kt1::KeyedTable{KT,TT}, kt2::KeyedTable{KT,TT}) where {KT,TT}
  n = length(kt1)
  for (i,x) in enumerate(_keys(kt2))
    if x != nothing
      @assert !(x ∈ keys(kt1))
      _index(kt1)[x] = i + n
    end
  end
  append!(_table(kt1), _table(kt2))
  append!(_keys(kt1), _keys(kt2))
end

Base.getindex(kt::KeyedTable, i::Int) = Tables.rows(_table(kt))[i]

Base.getindex(kt::KeyedTable{KT}, i::KT) where {KT} = Tables.rows(_table(kt))[_index(kt)[i]]

Base.getindex(kt::KeyedTable, i::Int, nm::Symbol) = kt[i][nm]

Base.getindex(kt::KeyedTable{KT}, i::KT, nm::Symbol) where {KT} = kt[i][nm] 

Base.setindex!(kt::KeyedTable, v, i::Int) = setindex!(_table(kt), v, i)

Base.setindex!(kt::KeyedTable{KT}, v, i::KT) where {KT} = setindex!(_table(kt), v, _index(kt)[i])

Base.setindex!(kt::KeyedTable, v, i::Int, nm::Symbol) = setindex!(getproperty(_table(kt), nm), v, i)

Base.setindex!(kt::KeyedTable{KT}, v, i::KT, nm::Symbol) where {KT} =
  setindex!(getproperty(_table(kt), nm), v, _index(kt)[i])

Base.keys(kt::KeyedTable) = keys(_index(kt))

Base.length(kt) = length(_table(kt))

key(kt::KeyedTable,i::Int) = _keys(kt)[i]

index(kt::KeyedTable{KT}, key::KT) where {KT} = _index(kt)[key]

function setkey(kt::KeyedTable{KT},i::Int,key::KT) where {KT}
  @assert !(key ∈ keys(kt))
  _keys(kt)[i] = key
  _index(kt)[key] = i
end

setkey(kt::KeyedTable{KT},oldkey::KT,newkey::KT) where {KT} = setkey(kt,index(kt,oldkey),newkey)

end
