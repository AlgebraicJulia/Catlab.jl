module Colimits 

using StructEquality

using .....BasicSets
import .....Theories: initial, ⊕, coproduct

using ....Cats, ....SetCats
using ....Cats.FreeDiagrams: DiagramImpl
import ....Cats: limit, colimit
import ....Cats.LimitsColimits: _universal


using ...ACSetTransformations, ...CSets

using ..LimitsColimits: unpack_diagram, pack_components, unpack_components, unpack_sets

# Structs
#########
""" Colimit of attributed C-sets that stores the pointwise colimits in Set.
"""
@struct_hash_equal struct ACSetColimit <: ColimitImpl
  cocone::Multicospan
  colimits::NamedTuple
end

# """ Why was this defined but not something analogous in Limits? """
# function universal(colim::ACSetColimit, cocone::Multicospan)
#   X = apex(cocone)
#   S, Ts = acset_schema(X), datatypes(X)
#   ud = unpack_diagram(cocone; S=S, Ts=Ts, var=true)
#   components = Dict(k=>collect(universal(colim.colimits[k], ud[k])) for k in keys(ud))
#   ACSetTransformation(ob(colim), apex(cocone); components...)
# end

# Dispatchx
##########

colimit(d::DiagramImpl, c::CatOfACSet, alg; kw...) = 
  colimit(d, getvalue(c), alg; kw...)

colimit(d::DiagramImpl, c::ACSetCategory, alg; kw...) = 
  colimit(d, getvalue(c), alg; kw...)


# CSetCats
##########

function colimit(diagram, m::CSetCat, a::DefaultAlg)
  Xs = cocone_objects(diagram)
  colimits = map(x-> colimit(x, SetC(),a), unpack_diagram(diagram, m))
  pack_colimit(m, diagram, Xs, colimits)
end

function _universal(::DiagramImpl, m::CSetCat{S}, colim::ACSetColimit, 
                    cocone::Multicospan) where S
  components = map(universal, colim.colimits, unpack_diagram(cocone, m))
  ACSetTransformation(components, ob(colim), apex(cocone))
end

""" Make colimit of acsets from colimits of sets, ignoring attributes.
"""
function pack_colimit(cat::CSetCat{S}, diagram, Xs, colimits) where S
  Y = cat.constructor()
  set = Category(TypeCat(SetC()))
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in homs(S)
    Yfs = map(zip(legs(colimits[d]), Xs)) do (ι, X) 
      Xc, Xd = get_ob[cat](X, c), get_ob[cat](X, d)
      compose(set, get_hom[cat](X, f, Xc, Xd), ι)
    end
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs))
  impl = ACSetColimit(Multicospan(Y, ιs), colimits)
  diag_cat = Category(TypeCat(CatOfACSet(ACSetCategory(cat))))
  Colimit(Diagram(diagram, diag_cat), impl)
end

# ACSetCats 
###########

function colimit(diagram, m::ACSetCat, a::DefaultAlg)
  Xs = cocone_objects(diagram)
  @show unpack_diagram(diagram, m)
  colimits = map(x-> colimit(x, SetC(), a), unpack_diagram(diagram, m))
  pack_colimit(m, diagram, Xs, colimits)
end

""" Make colimit of acsets from colimits of sets, ignoring attributes.
"""
function pack_colimit(cat::ACSetCat{S}, diagram, Xs, colimits) where S
  Y = cat.constructor()
  set = Category(TypeCat(SetC()))
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in homs(S)
    Yfs = map(zip(legs(colimits[d]), Xs)) do (ι, X) 
      Xc, Xd = get_ob[cat](X, c), get_ob[cat](X, d)
      compose(set, get_hom[cat](X, f, Xc, Xd), ι)
    end
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs))

  for (attr, c, d) in attrs(S)
    data = fill(nothing, nparts(Y, c))
    for (ι, X) in zip(ιs, Xs)
      ιc, ιd = ι[c], ι[d]
      for i in parts(X, c)
        j = ιc(i)
        if isnothing(data[j])
          data[j] = Some(ιd(subpart(X, i, attr)))
        else
          val1, val2 = ιd(subpart(X, i, attr)), something(data[j])
          val1 == val2 || error(
            "ACSet colimit does not exist: $attr attributes $val1 != $val2")
        end
      end
    end
    set_subpart!(Y, attr, map(something, data))
  end

  impl = ACSetColimit(Multicospan(Y, ιs), colimits)
  diag_cat = Category(TypeCat(CatOfACSet(ACSetCategory(cat))))
  Colimit(Diagram(diagram, diag_cat), impl)
end


""" Set data attributes of colimit of acsets using universal property.
"""
function colimit_attrs!(colim,S,Ts, Xs) 
  Y, ιs = ob(colim), legs(colim)
  for (attr, c, d) in attrs(S)
    T = attrtype_instantiation(S, Ts, d)
    data = Vector{Union{Some{Union{T,AttrVar}},Nothing}}(nothing, nparts(Y, c))
    for (ι, X) in zip(ιs, Xs)
      ιc, ιd = ι[c], ι[d]
      for i in parts(X, c)
        j = ιc(i)
        if isnothing(data[j])
          data[j] = Some(ιd(subpart(X, i, attr)))
        else
          val1, val2 = ιd(subpart(X, i, attr)), something(data[j])
          val1 == val2 || error(
            "ACSet colimit does not exist: $attr attributes $val1 != $val2")
        end
      end
    end
    set_subpart!(Y, attr, map(something, data))
  end
  colim
end



# if abstract_product 
#   # Create attrvars for each distinct combination of projection values
#   for c in objects(S)
#     seen = Dict()
#     for part in parts(Y, c)
#       for (f, _, d) in attrs(S; from=c)
#         monoid = haskey(attrfun, f) ? attrfun[f] : get(attrfun, d, nothing)
#         vals = [X[l(part),f] for (l,X) in zip(legs(limits[c]),cone_objects(diagram))]
#         if isnothing(monoid)
#           if !haskey(seen, vals)
#             seen[vals] = add_part!(Y,d)
#           end
#           set_subpart!(Y, part, f, AttrVar(seen[vals]))
#         else 
#           set_subpart!(Y, part, f, monoid(vals))
#         end
#       end
#     end
#   end
#   # Handle attribute components
#   alim = NamedTuple(Dict(map(attrtypes(S)) do at 
#     T = attrtype_type(Y, at)
#     apx = VarSet{T}(nparts(Y, at))
#     at => begin 
#       vfs = VarFunction{T}[]
#       for (i,X) in enumerate(cone_objects(diagram))
#         v = map(parts(Y,at)) do p 
#           f, c, j = var_reference(Y, at, p)
#           X[legs(limits[c])[i](j), f]
#         end
#         push!(vfs,VarFunction{T}(v, FinSet(nparts(X, at))))
#       end
#       Multispan(apx,vfs)
#     end
#   end))
# else
#   alim = NamedTuple()
# end 


# LooseACSetCats
################

struct LooseACSetCat end # PLACEHOLDER 

function colimit(diagram, ::LooseACSetCat, ::DefaultAlg;
                 type_components=nothing)
  isnothing(type_components) &&
    error("Colimits of loose acset transformations are not supported " *
          "unless attrtype components of coprojections are given explicitly")

  ACSUnionAll = Base.typename(ACS).wrapper
  ColimitACS = ACSUnionAll{
    (mapreduce(tc -> eltype(codom(tc[d])), typejoin, type_components)
     for d in attrtypes(S))...}

  colimits = map(colimit, unpack_diagram(diagram; S=S, Ts=Ts))
  Xs = cocone_objects(diagram)
  colimit_attrs!(pack_colimit(ColimitACS, S, diagram, Xs, colimits; 
                              type_components=type_components), S,Ts,Xs)
end



end # module
