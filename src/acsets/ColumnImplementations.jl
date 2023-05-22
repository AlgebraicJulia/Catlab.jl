module ColumnImplementations
export column_type, indexchoice,
  HomChoice, AttrChoice, NoIndex, Index, UniqueIndex, Sparse, Dense, AttrVar 

using MLStyle
using StructEquality
using ..IndexUtils
using ..Columns


"""
Maps from attribute variables can go into arbitrary Julia types or other 
variables (indexed by integers). This wrapper types allows us to not confuse 
our Attr Variable indices with the Julia type of Int
"""
@struct_hash_equal struct AttrVar 
  val::Int 
end 
Base.isless(x::AttrVar,y::AttrVar) = x.val < y.val
Base.convert(::Type{T}, x::T) where {T>:Union{Nothing,AttrVar}} = x
Base.convert(::Type{T}, x::T) where {T>:AttrVar} = x
Base.convert(::Type{T}, x) where {T>:AttrVar} = convert(Base.typesplit(T, AttrVar), x)


# Column types for acsets
#########################

# There are many ways to mix and match mappings and preimage mappings
# Here we present a way of constructing sensible defaults for ACSets
# We make these concrete struct types for ease of debugging
#
# Note: maybe these could be generated with a macro?

"""
A column for a vec-backed unindexed hom
"""
struct DenseFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::VecMap{Int, V}
  pc::TrivialCache{Int, Int}
end

"""
A column for a vec-backed indexed hom
"""
struct DenseIndexedFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::VecMap{Int, V}
  pc::StoredPreimageCache{Int, Int, SortedSet{Int},
                         VecMap{SortedSet{Int}, Vector{SortedSet{Int}}}}
end


"""
A column for a vec-backed injective hom
"""
struct DenseInjectiveFinColumn{V<:AbstractVector{Int}} <: Column{Int,Int}
  m::VecMap{Int, V}
  pc::InjectiveCache{Int, Int, VecMap{Int, Vector{Int}}}
end

# Compatibility hack to support unique_index
function Columns.preimage(dom, c::DenseInjectiveFinColumn, y::Int, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed homomorphisms"
  get(c.pc.inverse, y, 0)
end

function Columns.preimage_multi(dom, c::DenseInjectiveFinColumn, ys, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed homomorphisms"
  view_with_default(c.pc.inverse, ys, DefaultVal{0})
end


"""
A column for a dict-backed unindexed hom with key type K
"""
struct SparseFinColumn{K, D<:AbstractDict{K,K}} <: Column{K,K}
  m::DictMap{K, K, D}
  pc::TrivialCache{K, K}
end

"""
A column for a dict-backed indexed hom with key type K
"""
struct SparseIndexedFinColumn{K,D<:AbstractDict{K,K}} <: Column{K,K}
  m::DictMap{K, K, D}
  pc::StoredPreimageCache{K, K, Set{K},
                         DictMap{K, Set{K}, Dict{K,Set{K}}}}
end

"""
A column for a dict-backed injective hom with key type K
"""
struct SparseInjectiveFinColumn{K} <: Column{K,K}
  m::DictMap{K,K}
  pc::InjectiveCache{K,K,DictMap{K,K, Dict{K,K}}}
end

"""
A column for a vec-backed unindexed attr
"""
struct DenseColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::VecMap{T,V}
  pc::TrivialCache{Int,T}
  function DenseColumn{T, V}(m, pc) where {T,V}
    new{T,V}(m,pc)
  end
end

"""
A column for a vec-backed indexed attr
"""
struct DenseIndexedColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::VecMap{T,V}
  pc::StoredPreimageCache{Int,T,SortedSet{Int},
                          DictMap{T,SortedSet{Int},Dict{T,SortedSet{Int}}}}
end

"""
A column for a vec-backed unindexed attr
"""
struct DenseInjectiveColumn{T, V<:AbstractVector{T}} <: Column{Int,T}
  m::VecMap{T,V}
  pc::InjectiveCache{Int,T,DictMap{T,Int,Dict{T,Int}}}
end

# Compatibility hack
function Columns.preimage(dom, c::DenseInjectiveColumn{T}, y::T, ::UnboxInjectiveFlag) where {T}
  # @warn "using old convention for preimage of unique-indexed attributes"
  get(c.pc.inverse.d, y, 0)
end

function Columns.preimage_multi(dom, c::DenseInjectiveColumn, ys, ::UnboxInjectiveFlag)
  # @warn "using old convention for preimage of unique-indexed attributes"
  broadcast(ys) do y
    get(c.pc.inverse.d, y, 0)
  end
end

"""
A column for a dict-backed unindexed hom with key type K
"""
struct SparseColumn{K, T, D<:AbstractDict{K,T}} <: Column{K,T}
  m::DictMap{K, T, D}
  pc::TrivialCache{K, T}
end

"""
A column for a dict-backed indexed hom with key type K
"""
struct SparseIndexedColumn{K, T, D<:AbstractDict{K,T}} <: Column{K,T}
  m::DictMap{K, T, D}
  pc::StoredPreimageCache{K, T, Set{K}, DictMap{T, Set{K}, Dict{T, Set{K}}}}
end

"""
A column for a dict-backed injective hom with key type K
"""
struct SparseInjectiveColumn{K, T, D<:AbstractDict{K,T}} <: Column{K,T}
  m::DictMap{K,T,D}
  pc::InjectiveCache{K,T,DictMap{T,K,Dict{T,K}}}
end


@data HomOrAttr begin
  HomChoice
  AttrChoice(T::Any)
end

@data IndexChoice begin
  NoIndex
  Index
  UniqueIndex
end

@data Sparsity begin
  Dense
  Sparse(K::Any)
end

function column_type(hom_or_attr::HomOrAttr, index::IndexChoice, sparsity::Sparsity=Dense)
  @match hom_or_attr begin
    HomChoice => @match sparsity begin
      Dense => @match index begin
        NoIndex => DenseFinColumn{Vector{Int}}
        Index => DenseIndexedFinColumn{Vector{Int}}
        UniqueIndex => DenseInjectiveFinColumn{Vector{Int}}
      end
      Sparse(K) => @match index begin
        NoIndex => SparseFinColumn{K,Dict{K,K}}
        Index => SparseIndexedFinColumn{K,Dict{K,K}}
        UniqueIndex => SparseInjectiveFinColumn{K,Dict{K,K}}
      end
    end
    AttrChoice(T) => @match sparsity begin
      Dense => @match index begin
        NoIndex => DenseColumn{Union{AttrVar,T},Vector{Union{AttrVar,T}}}
        Index => DenseIndexedColumn{Union{AttrVar,T},Vector{Union{AttrVar,T}}}
        UniqueIndex => DenseInjectiveColumn{Union{AttrVar,T},Vector{Union{AttrVar,T}}}
      end
      Sparse(K) => @match index begin
        NoIndex => SparseColumn{K,Union{AttrVar,T},Dict{K,Union{AttrVar,T}}}
        Index => SparseIndexedColumn{K,Union{AttrVar,T},Dict{K,Union{AttrVar,T}}}
        UniqueIndex => SparseInjectiveColumn{K,Union{AttrVar,T},Dict{K,Union{AttrVar,T}}}
      end
    end
  end
end

"""
Convert specification of indexing via lists of indexed and unique_indexed
morphisms into a specific enum choice.
"""
indexchoice(f, index, unique_index) = if f ∈ unique_index
  UniqueIndex
elseif f ∈ index
  Index
else
  NoIndex
end

end
