module Limits 

using StructEquality

using .....BasicSets
import .....Theories: terminal, ⊗, product

using ....Cats
using ....Cats.FreeDiagrams: DiagramImpl
import ....Cats: limit, colimit
import ....Cats.LimitsColimits: _universal

using ...ACSetTransformations, ...CSets

using ..LimitsColimits: unpack_diagram, pack_components, unpack_components, unpack_sets

# Structs
#########

""" Limit of attributed C-sets that stores the pointwise limits in Set.
"""
@struct_hash_equal struct ACSetLimit <: LimitImpl
  cone::Multispan
  limits::NamedTuple
end

# Dispatch 
##########

limit(d::DiagramImpl, c::CatOfACSet, alg; kw...) = 
  limit(d, getvalue(c), alg; kw...)

limit(d::DiagramImpl, c::ACSetCategory, alg; kw...) = 
  limit(d, getvalue(c), alg; kw...)

# CSetCat 
#########
"""
Compute limits and colimits in C-Set by reducing to those in Set using the
"pointwise" formula for (co)limits in functor categories.
"""
function limit(diagram, m::CSetCat{S}, a::DefaultAlg) where S
  up = unpack_diagram(diagram, m)
  limits = map(x->limit(x,SetC(),a), up)
  Xs = cone_objects(diagram)
  pack_limit(m, diagram, Xs, limits)
end

function _universal(::DiagramImpl, m::CSetCat{S}, lim::ACSetLimit, 
                    cone::Multispan) where S
  components = map(universal, lim.limits, unpack_diagram(cone, m))
  ACSetTransformation(components, apex(cone), ob(lim))
end



""" Make limit of acsets from limits of underlying sets, ignoring attributes.

If one wants to consider the attributes of the apex, the following 
`type_components` - TBD
`abstract_product` - places attribute variables in the apex
`attrfun` - allows one to, instead of placing an attribute in the apex, apply 
            a function to the values of the projections. Can be applied to an
            AttrType or an Attr (which takes precedence).
"""
function pack_limit(cat::CSetCat{S}, diagram, Xs, limits) where {S}
  Y = cat.constructor()
  set = Category(TypeCat(SetC()))
  for c in objects(S)
    add_parts!(Y, c, length(ob(limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map(zip(legs(limits[c]), Xs)) do (π, X) 
      Xc, Xd = get_ob[cat](X, c), get_ob[cat](X, d)
      compose(set, π, get_hom[cat](X, f, Xc, Xd))
    end
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  πs = pack_components(map(legs, limits), map(X -> Y, Xs), Xs)
  impl = ACSetLimit(Multispan(Y, πs), limits)
  diag_cat = Category(TypeCat(CatOfACSet(ACSetCategory(cat))))
  Limit(Diagram(diagram, diag_cat), impl)
end

# ACSetCat 
##########

# LooseACSetCat 
###############

""" PLACEHOLDER """
struct LooseACSetCat end 

"""
A limit of a diagram of ACSets with LooseACSetTransformations.

For general diagram shapes, the apex of the categorical limit will not have
clean Julia types for its attributes, i.e. predicates will be needed to further 
constrain them. `product_attrs` must be turned on in order to avoid an error in 
cases where predicates would be needed. 

`product_attrs=true` will take a limit of the purely combinatorial data, and 
the attribute data of the apex is dictated purely by the ACSets that are have 
explicit cone legs: the value of an attribute (e.g. `f`) for the i'th part in  
the apex is the product `(f(π₁(i)), ..., f(πₙ(i)))` where π maps come from 
the combinatorial part of the limit legs. The type components of the j'th leg of 
the limit is just the j'th cartesian projection.
"""
function limit(diagram, ::LooseACSetCat, ::DefaultAlg; product_attrs::Bool=false)
  limits = map(limit, unpack_diagram(diagram, S=S, all=!product_attrs))
  Xs = cone_objects(diagram)

  attr_lims = (product_attrs ?
    map(limit, unpack_diagram(DiscreteDiagram(Xs, Hom), S=S, all=true)) : limits )

  LimitACS = if isempty(attrtypes(S)); ACS
  else
    ACSUnionAll = Base.typename(ACS).wrapper
    ACSUnionAll{(eltype(ob(attr_lims[d])) for d in attrtypes(S))...}
  end

  type_components = [
    Dict(d=>legs(attr_lims[d])[i] for d in attrtypes(S)) for i in eachindex(Xs)]

  limits = NamedTuple(k=>v for (k,v) in pairs(limits) if k ∈ objects(S))
  lim = pack_limit(LimitACS, diagram, Xs, limits;
                   type_components=type_components)
  Y = ob(lim)
  for (f, c, d) in attrs(S)
    Yfs = map((π, X) -> π ⋅ FinDomFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(attr_lims[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  lim
end

end # module