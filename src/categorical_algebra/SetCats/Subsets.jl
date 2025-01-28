module Subsets 

export SubFinSet, predicate, SubobjectElementWise

using StructEquality

using GATlab

using ....BasicSets
import ....BasicSets: force
using ....Theories: dom, codom
import ....Theories: ob, hom
using ...Cats: Subobject, Category, TypeCat, ThSubobjectLattice
import ...Cats.Subobjects: Subobject, meet, join, top, bottom

""" Subset of a finite set. """
const SubFinSet = Subobject{FinSet}

Subobject(X::FinSet, f) = Subobject(FinFunction(f, X))

SubFinSet(X, f) = Subobject(FinFunction(f, X))

force(A::SubFinSet) = Subobject(force(hom(A)))

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

""" 
Algorithms to compute subobject operations using elementwise boolean logic.
"""
struct SubobjectElementWise end 

@instance ThSubobjectLattice{Union{FinSetInt,FinSet},SubFinSet} [model::SubobjectElementWise ] begin

  meet(A::SubFinSet, B::SubFinSet) = 
    SubFinSet(predicate(A) .& predicate(B))

  join(A::SubFinSet, B::SubFinSet) = 
    SubFinSet(predicate(A) .| predicate(B))

  top(X::Union{FinSetInt,FinSet}) = SubFinSet(trues(length(X)))

  bottom(X::Union{FinSetInt,FinSet}) = SubFinSet(falses(length(X)))
end

end # module
