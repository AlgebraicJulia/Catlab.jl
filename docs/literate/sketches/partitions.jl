# # Partitions
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/sketches/Partitions.ipynb)
#
# Partitions are a categorical construction that we derive from sets and functions.
# Given a set A, you can think of all of the ways to partition A into parts.
# These ways of partitioning are isomorphic to equivalence relations R ⊆ A × A.

# The first step is our Catlab imports
using Core: GeneratedFunctionStub
using Test

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.CategoricalAlgebra.FinSets
import Catlab.Theories: compose
using DataStructures
using PrettyTables
PrettyTables.pretty_table(f::FinFunction, name::Symbol=:f) = pretty_table(OrderedDict(:x=>1:dom(f).set, Symbol("$(name)(x)")=>collect(f)))

# ## FinSet: the category of Finite Sets
# In FinSet the objects are sets n = {1...n} and the morphisms are functions between finite sets.
# You can wrap a plain old Int into a finite set with the FinSet(n::Int) function. These sets will
# serve as the domain and codomains of our functions.
n = FinSet(3)
m = FinSet(4)

# once you have some sets, you can define functions between them. A FinFunction from n to m, f:n→m, can be specified as
# an array of length n with elements from m.

f = FinFunction([2,4,3], n, m)

pretty_table(f)

# ## Surjective maps
# In order to use a map to represent a partition, we have to make sure that it is surjective.
# Given a FinFunction, we can compute the preimage of any element in its codomain. 

preimage(f, 2)

preimage(f, 1)

# If the preimage is empty, then there is no element in the domain that maps to that element of the codomain.
# This gives us a definition of surjective functions by asserting that all the preimages are nonempty.
# Julia note: !p is the predicate x ↦ ¬p(x), f.(A) applies f to all of the elements in A.

is_surjective(f::FinFunction) = all((!isempty).(preimage(f,i) for i in codom(f)))
is_surjective(f)

# Our function f, wasn't surjective so it can't be used to induce a partition via its preimages.
# Let's try again,

g = FinFunction([1,2,3,3], m, n)
pretty_table(g, :g)
is_surjective(g)

# # Refinements of a Partition
# When defining partitions classically as A = ∪ₚ Aₚ with p ≠ r ⟹ Aₚ ≠ Aᵣ,
# it is not immediately obvious how to define comparisons between partitions.
# With the "a partition of A is a surjective map out of A" definition, the comparisons
# are obvious. The composition of surjective maps is surjective, so we can define
# the refinement order in terms of a diagram in Set.
#
# <!-- https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzMsMCwiUSJdLFszLDIsIlAiXSxbMSwyLCJoIl0sWzAsMSwiZiJdLFswLDIsImciLDJdXQ== -->
# <iframe class="quiver-embed" src="https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzMsMCwiUSJdLFszLDIsIlAiXSxbMSwyLCJoIl0sWzAsMSwiZiJdLFswLDIsImciLDJdXQ==&embed" width="560" height="432" style="border-radius: 8px; border: none;"></iframe>

A = FinSet(4)
Q = FinSet(3)
P = FinSet(2)

f = FinFunction([1,2,3,3], A, Q)
g = FinFunction([1,1,2,2], A, P)
h = FinFunction([1,1,2], Q, P)

@test_throws ErrorException compose(g,h) 

pretty_table(compose(f,h), Symbol("(f⋅h)"))

compose(f,h) == g

# so f is a refinement of g.
# which means that g is coarser than f.


h′ = FinFunction([1,1], P, FinSet(1))

pretty_table(f⋅h⋅h′, Symbol("f⋅h⋅h′"))

# ### Properties of refinements
# We can show that refinement gives us a preorder on partitions directly from the
# nice properties of surjective maps.
# 1. Reflexive: Any partition is a refinement of itself.
# 2. Transitive: If f ≤ g ≤ h as partitions, then f ≤ h
# You can read these directly off the definition of refinements as a commutative
# triangle in the category of (Set, Surjections).
# <!-- https://q.uiver.app/?q=WzAsNCxbMCwwLCJBIl0sWzMsMCwiUSJdLFszLDIsIlAiXSxbMyw0LCJRXlxccHJpbWUiXSxbMSwyLCJoIl0sWzAsMSwiZiJdLFswLDIsImciLDJdLFsyLDMsImheXFxwcmltZSJdLFswLDMsImZcXGNkb3QgaFxcY2RvdCBoXlxccHJpbWUgPSBnXFxjZG90IGheXFxwcmltZSIsMl1d --> 
# <iframe class="quiver-embed" src="https://q.uiver.app/?q=WzAsNCxbMCwwLCJBIl0sWzMsMCwiUSJdLFszLDIsIlAiXSxbMyw0LCJRXlxccHJpbWUiXSxbMSwyLCJoIl0sWzAsMSwiZiJdLFswLDIsImciLDJdLFsyLDMsImheXFxwcmltZSJdLFswLDMsImZcXGNkb3QgaFxcY2RvdCBoXlxccHJpbWUgPSBnXFxjZG90IGheXFxwcmltZSIsMl1d&embed" width="560" height="688" style="border-radius: 8px; border: none;"></iframe>