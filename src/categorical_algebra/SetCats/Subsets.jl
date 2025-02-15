module Subsets

export SubFinSet, SubOpBoolean, predicate

using StructEquality

using ....Theories, ....BasicSets
import ....Theories: meet, join, top, bottom
using ...Cats 
import ...Cats: Subobject, hom, force, ob
using ...Cats.Subobjects: SubobjectHom
using ..VarFunctions

""" Subset of a finite set.
"""
const SubFinSet{S,T} = Subobject{<:FinSet{S,T}}

Subobject(X::FinSet, f) = Subobject(FinFunction(f, X))
SubFinSet(X, f) = Subobject(FinFunction(f, X))

force(A::SubFinSet{Int}) = Subobject(force(hom(A)))
Base.collect(A::SubFinSet) = collect(hom(A))
Base.sort(A::SubFinSet) = SubFinSet(ob(A), sort(collect(A)))

const AbstractBoolVector = Union{AbstractVector{Bool},BitVector}

""" Subset of a finite set represented as a boolean vector.

This is the subobject classifier representation since `Bool` is the subobject
classifier for `Set`.
"""
@struct_hash_equal struct SubFinSetVector{S<:FinSet} <: Subobject{S}
  set::S
  predicate::AbstractBoolVector

  function SubFinSetVector(X::S, pred::AbstractBoolVector) where S<:FinSet
    length(pred) == length(X) ||
      error("Size of predicate $pred does not equal size of object $X")
    new{S}(X, pred)
  end
end

Subobject(X::FinSet, pred::AbstractBoolVector) = SubFinSetVector(X, pred)
SubFinSet(pred::AbstractBoolVector) = Subobject(FinSet(length(pred)), pred)

ob(A::SubFinSetVector) = A.set
hom(A::SubFinSetVector) = FinFunction(findall(A.predicate), A.set)
predicate(A::SubFinSetVector) = A.predicate

function predicate(A::SubFinSet)
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    pred[f(x)] = true
  end
  pred
end

function predicate(A::SubobjectHom{<:VarSet}) 
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    fx = f(x)
    if fx isa AttrVar
      pred[fx.val] = true
    end
  end
  pred
end

@instance ThSubobjectLattice{FinSet,SubFinSet} begin
  @import ob
  meet(A::SubFinSet, B::SubFinSet) = meet(A, B, SubOpBoolean())
  join(A::SubFinSet, B::SubFinSet) = join(A, B, SubOpBoolean())
  top(X::FinSet) = top(X, SubOpWithLimits())
  bottom(X::FinSet) = bottom(X, SubOpWithLimits())
end

""" Algorithm to compute subobject operations using elementwise boolean logic.
"""
struct SubOpBoolean <: SubOpAlgorithm end

meet(A::SubFinSet{Int}, B::SubFinSet{Int}, ::SubOpBoolean) =
  SubFinSet(predicate(A) .& predicate(B))
join(A::SubFinSet{Int}, B::SubFinSet{Int}, ::SubOpBoolean) =
  SubFinSet(predicate(A) .| predicate(B))
top(X::FinSet{Int}, ::SubOpBoolean) = SubFinSet(trues(length(X)))
bottom(X::FinSet{Int}, ::SubOpBoolean) = SubFinSet(falses(length(X)))

end # module