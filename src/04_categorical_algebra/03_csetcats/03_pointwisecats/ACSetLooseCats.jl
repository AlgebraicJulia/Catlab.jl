
""" Loose transformation between attributed C-sets.

Limits and colimits in the category of attributed C-sets and loose homomorphisms
are computed pointwise on both objects *and* attribute types. This implies that
(co)limits of Julia types must be computed. Due to limitations in the
expressivity of Julia's type system, only certain simple kinds of (co)limits,
such as products, are supported.

Alternatively, colimits involving loose acset transformations can be constructed
with respect to explicitly given attribute type components for the legs of the
cocone, via the keyword argument `type_components` to `colimit` and related
functions. This uses the universal property of the colimit. To see how this
works, notice that a diagram of acsets and loose acset transformations can be
expressed as a diagram D: J → C-Set (for the C-sets) along with another diagram
A: J → C-Set (for the attribute sets) and a natural transformation α: D ⇒ A
(assigning attributes). Given a natural transformation τ: A ⇒ ΔB to a constant
functor ΔB, with components given by `type_components`, the composite
transformation α⋅τ: D ⇒ ΔB is a cocone under D, hence factors through the
colimit cocone of D. This factoring yields an assigment of attributes to the
colimit in C-Set.

For the distinction between tight and loose, see [`ACSetTranformation`](@ref).
"""
struct ACSetLoose end

# TODO