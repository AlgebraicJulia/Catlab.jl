using ..PointwiseCats: var_reference

""" Limit of attributed C-sets that stores the pointwise limits in Set.
"""
@struct_hash_equal struct ACSetLimit{Ob <: ACSet, Diagram,
    Cone <: Multispan{Ob}, Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

⊗(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊗, xs; init=apex(terminal(T)))

terminal(::Type{T}; loose=false, cset=false, kw...) where T <: ACSet =
  limit(EmptyDiagram{T}(kw_type(;loose, cset)); kw...)

product(X::ACSet, Y::ACSet; loose=false, cset=false,kw...) =
  limit(ObjectPair(X, Y, kw_type(;loose, cset)); kw...)
  
product(Xs::AbstractVector{<:ACSet}; loose=false, cset=false, kw...) =
  limit(DiscreteDiagram(Xs, kw_type(;loose, cset)); kw...)


# Compute limits and colimits in C-Set by reducing to those in Set using the
# "pointwise" formula for (co)limits in functor categories.

function limit(::Type{<:Tuple{ACS,<:TightACSetTransformation}}, diagram) where
    {S, ACS <: StructACSet{S}}
  isempty(attrtypes(S)) || error("Cannot take limit of ACSets with ACSetTransformations")
  limits = map(limit, unpack_diagram(diagram; S=S))
  Xs = cone_objects(diagram)
  pack_limit(ACS, diagram, Xs, limits)
end

"""
Variables are used for the attributes in the apex of limit of CSetTransformations
when there happen to be attributes. However, a commutative monoid on the 
attribute type may be provided in order to avoid introducing variables.
"""
function limit(::Type{<:Tuple{ACS,CSetTransformation}}, diagram; attrfun=(;)) where
  {S, ACS <: StructACSet{S}}
  limits = map(limit, unpack_diagram(diagram; S=S))
  Xs = cone_objects(diagram)
  pack_limit(ACS, diagram, Xs, limits; abstract_product=true, attrfun)
end


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
function limit(::Type{Tuple{ACS,Hom}}, diagram; product_attrs::Bool=false) where
    {S, ACS <: StructACSet{S}, Hom <: LooseACSetTransformation}
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

""" Make limit of acsets from limits of underlying sets, ignoring attributes.

If one wants to consider the attributes of the apex, the following 
`type_components` - TBD
`abstract_product` - places attribute variables in the apex
`attrfun` - allows one to, instead of placing an attribute in the apex, apply 
            a function to the values of the projections. Can be applied to an
            AttrType or an Attr (which takes precedence).
"""
function pack_limit(::Type{ACS}, diagram, Xs, limits; abstract_product=false, 
                    attrfun=(;), type_components=nothing
                   ) where {S, ACS <: StructACSet{S}}
  Y = ACS()
  for c in objects(S)
    add_parts!(Y, c, length(ob(limits[c])))
  end
  for (f, c, d) in homs(S)
    Yfs = map((π, X) -> π ⋅ FinFunction(X, f), legs(limits[c]), Xs)
    Yf = universal(limits[d], Multispan(ob(limits[c]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  if abstract_product 
    # Create attrvars for each distinct combination of projection values
    for c in objects(S)
      seen = Dict()
      for part in parts(Y, c)
        for (f, _, d) in attrs(S; from=c)
          monoid = haskey(attrfun, f) ? attrfun[f] : get(attrfun, d, nothing)
          vals = [X[l(part),f] for (l,X) in zip(legs(limits[c]),cone_objects(diagram))]
          if isnothing(monoid)
            if !haskey(seen, vals)
              seen[vals] = add_part!(Y,d)
            end
            set_subpart!(Y, part, f, AttrVar(seen[vals]))
          else 
            set_subpart!(Y, part, f, monoid(vals))
          end
        end
      end
    end
    # Handle attribute components
    alim = NamedTuple(Dict(map(attrtypes(S)) do at 
      T = attrtype_type(Y, at)
      apx = VarSet{T}(nparts(Y, at))
      at => begin 
        vfs = VarFunction{T}[]
        for (i,X) in enumerate(cone_objects(diagram))
          v = map(parts(Y,at)) do p 
            f, c, j = var_reference(Y, at, p)
            X[legs(limits[c])[i](j), f]
          end
          push!(vfs,VarFunction{T}(v, FinSet(nparts(X, at))))
        end
        Multispan(apx,vfs)
      end
    end))
  else
    alim = NamedTuple()
  end 
  πs = pack_components(map(legs, merge(limits,alim)), map(X -> Y, Xs), Xs; 
                       type_components=type_components)
  ACSetLimit(diagram, Multispan(Y, πs), limits)
end

function universal(lim::ACSetLimit, cone::Multispan)
  X = apex(cone)
  S, Ts = acset_schema(X), datatypes(X)
  components = map(universal, lim.limits, unpack_diagram(cone; S=S, Ts=Ts))
  acomps = Dict(map(filter(a->nparts(X,a)>0,attrtypes(S))) do at 
    at => map(parts(X,at)) do p 
      f, c, i = var_reference(X, at, p)
      ob(lim)[components[c](i), f]
    end
  end)
  ACSetTransformation(merge(components,acomps), apex(cone), ob(lim))
end
