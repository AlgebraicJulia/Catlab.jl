module Sheaves

using StructEquality
using LinearAlgebra
using SparseArrays
using ...BasicSets, ...CategoricalAlgebra
using ...CategoricalAlgebra.Misc.Matrices
using ...Theories
import ...Theories: dom, codom, id, ob, hom
import ...CategoricalAlgebra: legs, apex

export AbstractSheaf, AbstractFunctor, AbstractCover, AbstractCoverage,
  FinSetCat, FinVect, FinSetOp, FinSetOpT,
  FVectPullback, FVectPushforward,
  FMatPullback, FMatPushforward,
  ColimCover, DiagramTopology, is_coverage,
  Sheaf, diagnose_match, extend, restrict, MatchingError, MatchingFailure

Base.zeros(T, n::FinSet) = zeros(T, length(n))
direct_sum(vs) = reduce(vcat, vs)

abstract type AbstractSheaf end
abstract type AbstractFunctor end
abstract type AbstractCover end
abstract type AbstractCoverage end

@struct_hash_equal struct Sieve{T} <: AbstractCover
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

@struct_hash_equal struct ColimCover <: AbstractCover
  colimit::AbsColimit
end

ColimCover(d::FreeDiagram) = ColimCover(colimit[SkelFinSet()](getvalue(d)))

legs(s::ColimCover) = legs(s.colimit)
apex(s::ColimCover) = apex(s.colimit)
Base.enumerate(s::ColimCover) = enumerate(legs(s))

@struct_hash_equal struct DiagramTopology <: AbstractCoverage end

function is_coverage(top::AbstractCoverage, S::AbstractCover, object) 
  error("To implement a GTopology, you have to be able to check if a Sieve covers an object.")
end

function is_coverage(::DiagramTopology, S::ColimCover, object)
  apex(S) == object
end

@struct_hash_equal struct Sheaf{T<:AbstractCoverage,F<:Functor} <: AbstractSheaf
  coverage::T
  functor::F
end

coverage(s::Sheaf) = s.coverage
functor(s::Sheaf) = s.functor

abstract type AbstractSection end

@struct_hash_equal struct Section{S,D,V} <: AbstractSection
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
This is to apply the sheaf's functor to the morphism f and then apply that 
function to the data supplied. We can assume that you can directly call that 
applied functor on data, because sheaves take C to **Set**.
"""
function restrict(X::AbstractSheaf, s::Data, f::Hom) where {Data, Hom}
  hom_map(functor(X), f)(s)
end

"""    extend(X::AbstractSheaf, cover::AbstractCover, sections::AbstractVector)

Extend a collection of sections to the unique section that restricts to the 
sections provided. The `sections` vector needs to be indexed in the same order 
as `enumerate(cover)`.
"""
##################################
# THIS SHOULD BE DONE WITH A GAT # 
##################################
# function extend(X::AbstractSheaf, cover::AbstractCover, sections::AbstractVector)
#   error("In order to define a sheaf, you must implement restrict and extend")
# end

"""    MatchingFailure

A type for when sections over a sheaf fail to match, that is when they don't 
agree on the overlaps implied by a cover.
"""
@struct_hash_equal struct MatchingFailure
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
@struct_hash_equal struct MatchingError{T} <: Exception where T<:MatchingFailure
  failures::Vector{T}
end

function Base.show(io::IO, m::MatchingError)
  println(io, "$(typeof(m).name.name): Sections don't match on $(length(m.failures)) overlaps:")
  map(m.failures) do f
    show(io, f)
  end
end


"""    diagnose_match(X::Sheaf, cover, sections)

For each object X in the diagram, check that all the sections restrict to the same value along the Hom(X, -).

The arguments have the same interpretation as in `extend`.
"""
function diagnose_match(X::Sheaf, cover, sections)
  match_errors = MatchingFailure[]
  for (i,l₁) in enumerate(cover)
    for (j,l₂) in enumerate(cover)
      # we only need to check the upper triangle. i < j.
      if i >= j 
        continue
      end
      P = pullback[SkelFinSet()](l₁,l₂)
      @debug "Computing intersection of opens $i,$j"
      @debug apex(P)
      v₁ = restrict(X, sections[i], legs(P)[1])
      v₂ = restrict(X, sections[j], legs(P)[2])
      v₁ == v₂ || push!(match_errors, MatchingFailure(X, l₁, l₂, sections[i], sections[j], v₁, v₂))
    end
  end
  return match_errors
end

include("FVect.jl")

end # module
