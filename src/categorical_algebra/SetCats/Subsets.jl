module Subsets 

export SubFinSet, SubOpBoolean

using StructEquality

using GATlab

using ...Cats.Subobjects 
import ...Cats.Subobjects: Subobject, meet, join, top, bottom
using ...BasicSets.FinSets, ...BasicSets.FinFunctions
using ...BasicSets.SetFunctions: SetC
import ...BasicSets.FinFunctions: force
using ....Theories: dom, codom
import ....Theories: ob, hom

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


# function predicate(A::SubobjectHom{<:VarSet}) 
#   f = hom(A)
#   pred = falses(length(codom(f)))
#   for x in dom(f)
#     fx = f(x)
#     if fx isa AttrVar
#       pred[fx.val] = true
#     end
#   end
#   pred
# end

function predicate(A::SubFinSet)
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    pred[f(x)] = true
  end
  pred
end

@instance ThSubobjectLattice{FinSet,SubFinSet} begin
  @import ob
  meet(A::SubFinSet, B::SubFinSet) = meet(A, B, SetC(), SubOpBoolean())
  join(A::SubFinSet, B::SubFinSet) = join(A, B, SetC(), SubOpBoolean())
  top(X::FinSet) = top(X, SetC(), SubOpWithLimits())
  bottom(X::FinSet) = bottom(X, SetC(), SubOpWithLimits())
end

""" Algorithm to compute subobject operations using elementwise boolean logic.
"""
struct SubOpBoolean <: SubOpAlgorithm end

meet(A::SubFinSet, B::SubFinSet, ::SetC, ::SubOpBoolean) =
  SubFinSet(predicate(A) .& predicate(B))
join(A::SubFinSet, B::SubFinSet, ::SetC, ::SubOpBoolean) =
  SubFinSet(predicate(A) .| predicate(B))
top(X::FinSet, ::SetC, ::SubOpBoolean) = SubFinSet(trues(length(X)))
bottom(X::FinSet, ::SetC, ::SubOpBoolean) = SubFinSet(falses(length(X)))


end # module