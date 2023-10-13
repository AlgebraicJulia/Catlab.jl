struct FinVect <: Category{FinSet, Function, SmallCatSize} end

"""    FVectPullback{T} where T <: Number

The contravariant free vector space functor. 
The returned function f✶ restricts via precomposition.
"""
struct FVectPullback <: Functor{FinSetOpT, FinVect} end
dom(::FVectPullback) = FinSetOpT
codom(::FVectPullback) = FinVect
do_ob_map(::FVectPullback, n::FinSet) = n
do_hom_map(::FVectPullback, f::FinFunction) = (v->v[f.(dom(f))])
# as a callable functor this would be: FVectPullback = Functor(identity, f->(v->v[f.(dom(f))]), OppositeCat(FinSetCat()), FinVect())

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
  FinSetCat(), FinVect()
)

const FinMat = TypeCat(MatrixDom, Matrix)
const FinMatT = typeof(FinMat)

# call a matrix on a vector multiplies by it.
function (M::SparseArrays.SparseMatrixCSC{Int64, Int64})(x::AbstractVector)
  M*x
end

function pullback_matrix(f::FinFunction)
    n = length(dom(f))
    sparse(1:n, f.(dom(f)), ones(Int,n), dom(f).n, codom(f).n)
end

function pushforward_matrix(f::FinFunction)
  pullback_matrix(f)'
end

struct FMatPullback <: Functor{FinSetOpT, FinMatT} end
dom(::FMatPullback) = FinSetOpT
codom(::FMatPullback) = FinMat
do_ob_map(::FMatPullback, n::FinSet) = MatrixDom{AbstractMatrix}(n.n)
do_hom_map(::FMatPullback, f::FinFunction) = pullback_matrix(f)

FMatPushforward = Functor(n->MatrixDom(n.n),
  pushforward_matrix,
  FinSetCat(), FinVect()
)

"""    extend(X::Sheaf{T, FVectPullback}, cover::ColimCover, sections::Vector{Vector{R}}; check=true, debug=false) where {T<:DiagramTopology, R}

This method implements the extension operation for the diagram topology on FinSet for the Free Vector Space functor.
The implementation does copies the value of the ith section into the jth spot as indicated by the legs of the cocone.
"""
function extend(X::Sheaf{T, FVectPullback}, cover::ColimCover, sections::Vector{Vector{R}}; check=true, debug=false) where {T<:DiagramTopology, R}
  length(sections) == length(legs(cover)) || throw(ArgumentError("There are $(length(sections)) but only $(length(legs(cover))) legs in the cover"))
  v = zeros(R, apex(cover))
  if check
    match_errors = diagnose_match(X, cover, sections; debug=debug)
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

function extend(X::Sheaf{T, FMatPullback}, cover::ColimCover, sections::Vector{Vector{R}};check=true, debug=false) where {T<:DiagramTopology, R}
  length(sections) == length(legs(cover)) || throw(ArgumentError("There are $(length(sections)) but only $(length(legs(cover))) legs in the cover"))
  v = zeros(R, apex(cover))
  if check
    match_errors = diagnose_match(X, cover, sections; debug=debug)
    length(match_errors) == 0 || throw(MatchingError(match_errors))
  end
  f = copair(legs(cover))
  M = do_hom_map(functor(X), f)
  return Float64.(M) \ direct_sum(sections)
end
