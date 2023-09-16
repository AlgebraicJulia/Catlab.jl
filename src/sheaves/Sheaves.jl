module Sheaves
using LinearAlgebra
using SparseArrays
using ...CategoricalAlgebra
using ...CategoricalAlgebra.Categories
using ...CategoricalAlgebra.FinSets
using ...CategoricalAlgebra.Matrices
using ...GATs
using ...Theories
import ..CategoricalAlgebra.Categories: CatSize
import ...Theories: dom, codom, id, ob, hom
import ...CategoricalAlgebra: legs, apex
import ...CategoricalAlgebra.Categories: do_ob_map, do_hom_map

export AbstractSheaf, AbstractFunctor, AbstractCover, AbstractCoverage,
  FinSetCat, FinVect, FinSetOp, FinSetOpT,
  FVectPullback, FVectPushforward,
  FMatPullback, FMatPushforward,
  ColimCover, DiagramTopology, is_coverage,
  Sheaf, diagnose_match, extend, restrict, MatchingError, MatchingFailure


abstract type SmallCatSize <: CatSize end
Base.zeros(T, n::FinSet) = zeros(T, length(n))
direct_sum(vs) = reduce(vcat, vs)

abstract type AbstractSheaf end
abstract type AbstractFunctor end
abstract type AbstractCover end
abstract type AbstractCoverage end

struct FinSetCat <: Category{FinSet, FinFunction, SmallCatSize} end
struct FinVect <: Category{FinSet, Function, SmallCatSize} end

const FinSetOp = op(FinSetCat())
const FinSetOpT = typeof(FinSetOp)

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

struct Sieve{T} <: AbstractCover
  basis::T
end

Base.show(io::IO, S::AbstractCover) = begin
  print(io, "$(typeof(S))($(apex(S))):")
  for l in legs(S)
    print(io, "\n  ")
    show(io, l)
  end
end

legs(s::Sieve) = legs(s.basis)
apex(s::Sieve) = apex(s.basis)

struct ColimCover <: AbstractCover
  colimit
end

ColimCover(d::FreeDiagram) = ColimCover(colimit(d))

legs(s::ColimCover) = legs(s.colimit)
apex(s::ColimCover) = apex(s.colimit)
Base.enumerate(s::ColimCover) = enumerate(legs(s))

struct DiagramTopology <: AbstractCoverage end

function is_coverage(top::AbstractCoverage, S::AbstractCover, object) 
  error("To implement a GTopology, you have to be able to check if a Sieve covers an object.")
end

function is_coverage(::DiagramTopology, S::ColimCover, object)
  apex(S) == object
end

struct Sheaf{T<:AbstractCoverage,F<:Functor} <: AbstractSheaf
  coverage::T
  functor::F
end

coverage(s::Sheaf) = s.coverage
functor(s::Sheaf) = s.functor

abstract type AbstractSection end

struct Section{S,D,V} <: AbstractSection
  sheaf::S
  domain::D
  value::V
end


"""    restrict(X::AbstractSheaf, s::Section, f::Hom) where Hom

If you supply a wrapped section, you should get a back a wrapped section.
"""
function restrict(X::AbstractSheaf, s::Section, f::Hom) where Hom
  Section(X, domain(s), do_hom_map(functor(X), f)(value(s)))
end

"""    restrict(X::AbstractSheaf, s::Data, f::Hom) where {Data, Hom}

Restrict a section along a morphism in the sheaf.
This is to apply the sheaf's functor to the morphism f and then apply that function to the data supplied. 
We can assume that you can directly call that applied functor on data, because sheaves take C to **Set**.
"""
function restrict(X::AbstractSheaf, s::Data, f::Hom) where {Data, Hom}
  do_hom_map(functor(X), f)(s)
end

"""    extend(X::AbstractSheaf, cover::AbstractCover, sections::AbstractVector)

Extend a collection of sections to the unique section that restricts to the sections provided.
The `sections` vector needs to be indexed in the same order as `enumerate(cover)`.
"""
function extend(X::AbstractSheaf, cover::AbstractCover, sections::AbstractVector)
  error("In order to define a sheaf, you must implement restrict and extend")
end

"""    MatchingFailure

An type for when sections over a sheaf fail to match, that is when they don't agree on the overlaps implied by a cover.
"""
struct MatchingFailure
  sheaf::AbstractSheaf
  hom1
  hom2
  sec1
  sec2
  res1
  res2
end

Base.show(io::IO, m::MatchingFailure) = println(io, "$(typeof(m).name.name): Sections don't match on:\n\t$(m.hom1) and\n\t$(m.hom2)\n\t$(m.res1) ◁ $(m.sec1) but\n\t$(m.res2) ◁ $(m.sec2)")

"""    MatchingError

An Exception type for when sections over a sheaf fail to match, that is when they don't agree on the overlaps implied by a cover.
This stores the list MatchingFailures encountered when walking the cover.
"""
struct MatchingError{T} <: Exception where T<:MatchingFailure
  failures::Vector{T}
end

function Base.show(io::IO, m::MatchingError)
  println(io, "$(typeof(m).name.name): Sections don't match on $(length(m.failures)) overlaps:")
  map(m.failures) do f
    show(io, f)
  end
end


"""    diagnose_match(X::Sheaf, cover, sections; debug=false)

For each object X in the diagram, check that all the sections restrict to the same value along the Hom(X, -).

The arguments haave the same interpretation as in `extend`.
"""
function diagnose_match(X::Sheaf, cover, sections; debug=false)
  match_errors = MatchingFailure[]
  for (i,l₁) in enumerate(cover)
    for (j,l₂) in enumerate(cover)
      # we only need to check the upper triangle. i < j.
      if i >= j 
        continue
      end
      P = pullback(l₁,l₂)
      if debug
        println("Computing intersection of opens $i,$j")
        @show l₁
        @show l₂
        @show apex(P)
      end
      v₁ = restrict(X, sections[i], legs(P)[1])
      v₂ = restrict(X, sections[j], legs(P)[2])
      v₁ == v₂ || push!(match_errors, MatchingFailure(X, l₁, l₂, sections[i], sections[j], v₁, v₂))
    end
  end
  return match_errors
end

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

end

#=
W = @fincat begin
  A, B, C
  U, V
  ua: U → A
  ub: U → B
  vb: V → B
  vc: V → C
end

dW = @finfunctor W FinSet begin
  A => 3
  B => 2
  C => 3
  U => 2
  V => 1
  ua => [2,3]
  ub => [1,2]

  vb => [2]
  vc => [1]
end

@diagram FinSet{Int} begin
  v::FinSet(3)
end

function glue(X::CoSheaf{T, ContraFreeVect{T}}, cover, sections)
  f✶ = apply(FreeVect{T}(), copair(legs(cover.basis)))
  v = direct_sum(reduce(vcat, sections))
  return f✶(v)
end

struct FreeVect{T} <: AbstractFunctor where T<:Number end
const RVecPushforward = FreeVect{Float64}()

apply(F::FreeVect{T}, n::FinSet) where T = Vector{T}
apply(F::FreeVect{T}, f::FinFunction) where T = begin
  f✶(x) = map(dom(f)) do i
    sum(x[j] for j in preimage(f, i))
  end
  return f✶
end

struct ContraFreeVect{T} <: AbstractFunctor where T<:Number end

const RVec = ContraFreeVect{Float64}()

apply(F::ContraFreeVect{T}, n::FinSet) where T = Vector{T}
apply(F::ContraFreeVect{T}, f::FinFunction) where T = begin
  f✶(x) = x[f.(dom(f))]
  return f✶
end
=#