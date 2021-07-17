""" The algebra of subobjects in a topos.
"""
module Subobjects
export SubobjectFromLimits, subobject, meet, join, top, bottom

using StaticArrays: SVector

using ...Theories, ..Limits, ..CSets
import ...Theories: meet, join, top, bottom

# General subobjects
####################

""" Generic algorithm to compute subobject using limits and/or colimits.
"""
struct SubobjectFromLimits end

""" Meet (intersection) of subobjects.
"""
meet(f, g, ::SubobjectFromLimits) = meet(SVector(f,g), SubobjectFromLimits())

function meet(fs::AbstractVector, ::SubobjectFromLimits)
  lim = pullback(fs)
  compose(first(legs(lim)), first(fs)) # Arbitrary choice of first leg.
end

""" Join (union) of subobjects.
"""
join(f, g, ::SubobjectFromLimits) = join(SVector(f,g), SubobjectFromLimits())

function join(fs::AbstractVector, ::SubobjectFromLimits)
  lim = pullback(fs)
  colim = pushout(legs(lim))
  copair(colim, fs)
end

""" Top (full) subobject.
"""
top(X, ::SubobjectFromLimits) = id(X)

""" Bottom (empty) subobject.
"""
bottom(X::T, ::SubobjectFromLimits) where T = create(initial(T), X)

# Sub-C-sets
############

""" Construct subobject of C-set from components of inclusion map.

Recall that a *subobject* of a C-set ``X`` is a monomorphism ``α: U → X``. This
function constructs a subobject from the components of the monomorphism, given
as a named tuple or as keyword arguments.
"""
function subobject(X::T, components) where T <: AbstractACSet
  U = T()
  copy_parts!(U, X, components)
  ACSetTransformation(components, U, X)
end
subobject(X::AbstractACSet; components...) = subobject(X, (; components...))

end
