module ACSetColumns
export preimage, preimage_multi, clear_index!, clear_indices!, codom_hint!, IndexedVector, resize_clearing!

using ..IndexUtils

# An acset column should satisfy the following interface
#
# Base.getindex
# Base.setindex!
# Base.values
# clear_index!
# codom_hint!
# preimage
# preimage_multi
# resize_clearing!


"""
This function takes an acset column and an element of the domain and sets the column
value at that element be "missing"; 0 in the case of an integer, or nothing in the case
of a type that is a supertype of nothing. It also clears the index of the previous value
at the element.

The semantics of this function are deeply janky because we don't have proper support
for partial acsets; this will be fixed soon.
"""
function clear_index! end

"""
This is called to alert the column that there are new values in its codomain; the column
may then potentially preallocate some space for those new values.
"""
function codom_hint! end

"""
This gets the preimage of a single value in the codomain.
"""
function preimage end

"""
This gets the preimage of several values in the codomain. This is semantically equivalent
to broadcasting preimage, but a column implementation might instead return a view of
the index.
"""
function preimage_multi end

"""
This resizes a column, and if the column grows, initializes the new elements to the "missing"
value: 0 in the case of an integer or nothing in the case of a type that is a supertype of Nothing.

The semantics of this function are deeply janky because we don't have proper support for partial
acsets; this will be fixed soon. Specifically, if we have values that aren't a supertype of Nothing
or an integer, we get random uninitialized memory.
"""
function resize_clearing! end

# Additionally, the type should be able to be called with no arguments to create an empty column

function clear_indices!(v, idxs)
  for i in idxs
    clear_index!(v, i)
  end
end

function preimage(v::AbstractVector, x)
  findall(y -> x == y, v)
end

function preimage_multi(v::AbstractVector, xs)
  broadcast(x -> preimage(v,x), xs)
end

function clear_index!(v::AbstractVector{Int}, i::Int)
  v[i] = 0
end

function clear_index!(v::AbstractVector{T}, i::Int) where {T >: Nothing}
  v[i] = nothing
end

function clear_index!(v::AbstractVector{T}, i::Int) where {T}
end

function codom_hint!(v::AbstractVector{T}, n::Int) where {T}
end

function resize_clearing!(v::AbstractVector{Int}, n::Int)
  oldn = length(v)
  resize!(v, n)
  v[(oldn+1):n] .= 0
end

function resize_clearing!(v::AbstractVector{T}, n::Int) where {T}
  resize!(v, n)
end

struct IndexedVector{T,Index} <: AbstractVector{T}
  vals::Vector{T}
  index::Index
end

function IndexedVector{T,Index}() where {T,Index}
  IndexedVector{T,Index}(T[],Index())
end

Base.copy(v::IndexedVector{T,Index}) where {T,Index} =
  IndexedVector{T,Index}(copy(v.vals), deepcopy(v.index))

Base.size(v::IndexedVector) = size(v.vals)

function Base.getindex(v::IndexedVector{T}, i::Int) where {T}
  v.vals[i]
end

function Base.setindex!(v::IndexedVector{T}, x::T, i::Int) where {T}
  if isassigned(v.vals, i)
    oldx = v.vals[i]
    v.vals[i] = x
    update_index!(v.index, x, oldx, i)
  else
    v.vals[i] = x
    insert_index!(v.index, x, i)
  end
end

function insert_index!(index::Vector{Vector{Int}}, x::Int, i::Int)
  if x != 0
    insertsorted!(index[x], i)
  end
end

function insert_index!(index::Dict{T,Vector{Int}}, x::T, i::Int) where {T}
  if !isnothing(x)
    if x ∈ keys(index)
      insertsorted!(index[x],i)
    else
      index[x] = [i]
    end
  end
end

function insert_index!(index::Vector{Int}, x::Int, i::Int)
  if x != 0
    @assert index[x] == 0
    index[x] = i
  end
end

function insert_index!(index::Dict{T,Int}, x::T, i::Int) where {T}
  if !isnothing(x)
    @assert !(x ∈ keys(index))
    index[x] = i
  end
end

Base.values(v::IndexedVector) = v.vals

function update_index!(index::Vector{Vector{Int}}, x::Int, oldx::Int, i::Int)
  if 1 ≤ oldx ≤ length(index)
    deletesorted!(index[oldx], i)
  end
  insert_index!(index,x,i)
end

function update_index!(index::Dict{T,Vector{Int}}, x::T, oldx::T, i::Int) where {T}
  if oldx ∈ keys(index) # oldx could just be gobbledegook
    deletesorted!(index[oldx],i)
  end
  insert_index!(index,x,i)
end

function update_index!(index::Vector{Int}, x::Int, oldx::Int, i::Int)
  if oldx != 0
    index[oldx] = 0
  end
  insert_index!(index,x,i)
end

function update_index!(index::Dict{T,Int}, x::T, oldx::T, i::Int) where {T}
  if oldx ∈ keys(index)
    delete!(index, oldx)
  end
  insert_index!(index,x,i)
end

function resize_clearing!(v::IndexedVector{Int}, n::Int)
  oldn = length(v.vals)
  resize!(v.vals, n)
  v.vals[(oldn+1):n] .= 0
end

function resize_clearing!(v::IndexedVector{T}, n::Int) where {T}
  resize!(v.vals, n)
end

function clear_index!(v::IndexedVector{T}, i::Int) where {T >: Nothing}
  v[i] = nothing
end

function clear_index!(v::IndexedVector{Int}, i::Int)
  v[i] = 0
end

# There isn't an "empty" variable in this case, but we can still unset the index
function clear_index!(v::IndexedVector{T,Dict{T,Vector{Int}}}, i::Int) where {T}
  if isassigned(v.vals, i)
    oldx = v[i]
    if oldx ∈ keys(v.index)
      deletesorted!(v.index[oldx], i)
    end
  end
end

# There isn't an "empty" variable in this case, but we can still unset the index
function clear_index!(v::IndexedVector{T,Dict{T,Int}}, i::Int) where {T}
  if isassigned(v.vals, i)
    oldx = v[i]
    if oldx ∈ keys(v.index)
      delete!(v.index, oldx)
    end
  end
end

function preimage(v::IndexedVector{Int, <:Vector{<:Union{Int,Vector{Int}}}}, x::Int)
  v.index[x]
end

function preimage(v::IndexedVector{T, Dict{T, Vector{Int}}}, x) where {T}
  if x ∈ keys(v.index)
    v.index[x]
  else
    []
  end
end

function preimage(v::IndexedVector{T, Dict{T, Int}}, x) where {T}
  if x ∈ keys(v.index)
    v.index[x]
  else
    0
  end
end

function preimage_multi(v::IndexedVector{Int, <:Vector{<:Union{Int,Vector{Int}}}},
                  xs::Union{AbstractVector,UnitRange})
  @view v.index[xs]
end

function preimage_multi(v::IndexedVector{T, <:Dict{T, <:Union{Int,Vector{Int}}}},
                  xs::Union{AbstractVector,UnitRange}) where {T}
  [preimage(v, x) for x in xs]
end


function codom_hint!(v::IndexedVector{T}, n::Int) where {T}
  codom_hint_index!(v.index, n)
end

function codom_hint_index!(index::Vector{Vector{Int}}, n::Int)
  oldn = length(index)
  resize!(index, n)
  for i in (oldn + 1):n
    index[i] = Vector{Int}[]
  end
end

function codom_hint_index!(index::Vector{Int}, n::Int)
  oldn = length(index)
  resize!(index, n)
  index[(oldn + 1):n] .= 0
end

end
