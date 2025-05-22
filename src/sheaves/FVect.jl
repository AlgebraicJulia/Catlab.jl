using GATlab

@struct_hash_equal struct FinVect end

# The tests do not currently use the category structure of FinVect
@instance ThCategoryExplicitSets{FinSet, Function} [model::FinVect] begin
  dom(f::FinSet) = error()
  codom(f::FinSet) = error()
  id(f::FinSet) = error()
  compose(f::Function, g::Function) = error()
  ob_set() = SetOb(FinSet)
  hom_set() = SetOb(Function)
end

"""    FVectPullback{T} where T <: Number

The contravariant free vector space functor. 
The returned function f✶ restricts via precomposition.
"""
FVectPullback = Functor(identity, f->(v->v[f.(dom(f))]),
   op(Category(FinSetC())), Category(FinVect()))  # end {FinSetOpT, FinVect} end

"""    FreeVect{T} where T <: Number

The covariant free vector space functor. 
The returned  function f✶ sums over preimages.
"""
FVectPushforward = Functor(identity, # identity on objects
  # specify the pushforward construction
  f->(v->map(dom(f)) do i
    sum(v[j] for j in preimage(f,i))
  end),
  # covariant functor from FinSetCat to FinVect
  Category(FinSetC()), Category(FinVect())
)

@instance ThCategoryExplicitSets{Int, AbstractMatrix{T}
                                } [model::MatC{T}] where T begin 

  ob_set() = SetOb(PredicatedSet(Int, i -> i≥0))
  hom_set() = SetOb(AbstractMatrix{T})
end

# call a matrix on a vector multiplies by it.
function (M::SparseArrays.SparseMatrixCSC{Int64, Int64})(x::AbstractVector)
  M*x
end

function pullback_matrix(f::FinFunction)
  n = length(dom(f))
  sparse(1:n, f.(dom(f)), ones(Int,n), length(dom(f)), length(codom(f)))
end

function pushforward_matrix(f::FinFunction)
  pullback_matrix(f)'
end

FMatPullback = Functor(n -> length(n), f->pullback_matrix(f), 
  Category(SkelFinSet()), Category(MatC{Number}()))


FMatPushforward = Functor(n->MatrixDom(n.n),
  pushforward_matrix,
  Category(FinSetC()), Category(FinVect())
)

# The better way to do this is to make a ThSheaf and have different models 
# which implement `extend`
extend(X::Sheaf, cover, sections; kw...) = if functor(X) == FMatPullback 
  extend_mat(X,cover,sections; kw...)
elseif functor(X) == FVectPullback 
  extend_vect(X,cover,sections; kw...)
else 
  error("Cannot extend $X")
end

"""    extend(X::Sheaf{T}, cover::ColimCover, sections::Vector{Vector{R}}; check=true) where {T<:DiagramTopology, R}

This method implements the extension operation for the diagram topology on FinSet for the Free Vector Space functor.
The implementation does copies the value of the ith section into the jth spot as indicated by the legs of the cocone.
"""
function extend_vect(X::Sheaf{T}, cover::ColimCover, 
                    sections::Vector{Vector{R}}; check=true
                    ) where {T<:DiagramTopology, R}
  length(sections) == length(legs(cover)) || throw(ArgumentError(
    "There are $(length(sections)) but only $(length(legs(cover))) legs in the cover"))
  v = zeros(R, length(apex(cover)))
  if check
    match_errors = diagnose_match(X, cover, sections)
    length(match_errors) == 0 || throw(MatchingError(match_errors))
  end
  for (i, l) in enumerate(legs(cover))
    for j in dom(l)
      # copy the value of the ith section into the jth spot
      # last write wins is fine,
      # because the sections have to agree on the overlapping indices
      v[l(j)] = sections[i][j]
    end
  end
  return v
end


function extend_mat(X::Sheaf{T}, cover::ColimCover, 
                    sections::Vector{Vector{R}};check=true
                    ) where {T<:DiagramTopology, R}
  length(sections) == length(legs(cover)) || throw(ArgumentError(
    "There are $(length(sections)) but only $(length(legs(cover))) legs in the cover"))
  v = zeros(R, length(apex(cover)))
  if check
    match_errors = diagnose_match(X, cover, sections)
    length(match_errors) == 0 || throw(MatchingError(match_errors))
  end
  f = copair[TypedCatWithCoproducts(SkelFinSet())](legs(cover))
  M = hom_map(functor(X), f)
  return Float64.(M) \ direct_sum(sections)
end
