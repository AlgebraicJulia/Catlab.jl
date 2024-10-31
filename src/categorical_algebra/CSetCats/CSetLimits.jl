module CSetLimits 

# Limits and colimits
#####################

⊕(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊕, xs; init=apex(initial(T)))
⊗(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊗, xs; init=apex(terminal(T)))

""" Limit of attributed C-sets that stores the pointwise limits in Set.
"""
@struct_hash_equal struct ACSetLimit{Ob <: ACSet, Diagram,
    Cone <: Multispan{Ob}, Limits <: NamedTuple} <: AbstractLimit{Ob,Diagram}
  diagram::Diagram
  cone::Cone
  limits::Limits
end

""" Colimit of attributed C-sets that stores the pointwise colimits in Set.
"""
@struct_hash_equal struct ACSetColimit{Ob <: ACSet, Diagram,
    Cocone <: Multicospan{Ob}, Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

# By default, products of acsets are taken w.r.t. loose acset morphisms, whereas
# coproducts of acsets are taken w.r.t. tight acset morphisms. We do not need to
# provide defaults for limits and colimits of non-discrete diagrams, because the
# type of the diagram's morphisms disambiguates the situation.

kw_type(; loose::Bool=false, cset::Bool=false) = 
  if loose
    !cset || error("Cannot ask for a Loose CSetTransformation")
    LooseACSetTransformation
  elseif cset 
    CSetTransformation
  else 
    TightACSetTransformation
  end

Limits.terminal(::Type{T}; loose=false, cset=false, kw...) where T <: ACSet =
  limit(EmptyDiagram{T}(kw_type(;loose, cset)); kw...)
Limits.product(X::ACSet, Y::ACSet; loose=false, cset=false,kw...) =
  limit(ObjectPair(X, Y, kw_type(;loose, cset)); kw...)
Limits.product(Xs::AbstractVector{<:ACSet}; loose=false, cset=false, kw...) =
  limit(DiscreteDiagram(Xs, kw_type(;loose, cset)); kw...)

Limits.initial(::Type{T}; kw...) where T <: ACSet =
  colimit(EmptyDiagram{T}(TightACSetTransformation); kw...)
Limits.coproduct(X::ACSet, Y::ACSet; kw...) =
  colimit(ObjectPair(X, Y, TightACSetTransformation); kw...)
Limits.coproduct(Xs::AbstractVector{<:ACSet}; kw...) =
  colimit(DiscreteDiagram(Xs, TightACSetTransformation); kw...)

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

function colimit(::Type{<:Tuple{ACS,TightACSetTransformation}}, diagram) where {S,Ts,ACS <: StructACSet{S,Ts}}  
  colimits = map(colimit, unpack_diagram(diagram; S=S,Ts=Ts,var=true))
  Xs = cocone_objects(diagram)
  colimit_attrs!(pack_colimit(ACS, S, diagram, Xs, colimits), S, Ts, Xs)
end

function colimit(::Type{<:Tuple{DynamicACSet,TightACSetTransformation}}, diagram) 
  Xs = cocone_objects(diagram)
  X = first(Xs)
  S, Ts, ACS = acset_schema(X), datatypes(X), constructor(X)
  colimits = map(colimit, unpack_diagram(diagram; S=S, Ts=Ts, var=true))
  colimit_attrs!(pack_colimit(ACS, S, diagram, Xs, colimits), S, Ts, Xs)
end

# colimit(::Type{<:Tuple{VarSet,<:Any}}, diagram) = 
#   colimit(diagram, ToBipartiteColimit())

function colimit(::Type{<:Tuple{ACS,LooseACSetTransformation}}, diagram;
                 type_components=nothing) where {S,Ts, ACS<:StructACSet{S,Ts}}
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

""" Make colimit of acsets from colimits of sets, ignoring attributes.
"""
function pack_colimit(ACS,S, diagram, Xs, colimits; kw...)
  Y = ACS()
  for (c, colim) in pairs(colimits)
    add_parts!(Y, c, length(ob(colim)))
  end
  for (f, c, d) in homs(S)
    Yfs = map((ι, X) -> FinFunction(X, f) ⋅ ι, legs(colimits[d]), Xs)
    Yf = universal(colimits[c], Multicospan(ob(colimits[d]), Yfs))
    set_subpart!(Y, f, collect(Yf))
  end
  ιs = pack_components(map(legs, colimits), Xs, map(X -> Y, Xs); kw...)
  ACSetColimit(diagram, Multicospan(Y, ιs), colimits)
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

function universal(colim::ACSetColimit, cocone::Multicospan)
  X = apex(cocone)
  S, Ts = acset_schema(X), datatypes(X)
  ud = unpack_diagram(cocone; S=S, Ts=Ts, var=true)
  components = Dict(k=>collect(universal(colim.colimits[k], ud[k])) for k in keys(ud))
  ACSetTransformation(ob(colim), apex(cocone); components...)
end

""" Diagram in C-Set → named tuple of diagrams in Set.
"""
unpack_diagram(discrete::DiscreteDiagram{<:ACSet}; kw...) =
  map(DiscreteDiagram, unpack_sets(ob(discrete); kw...))
unpack_diagram(span::Multispan{<:ACSet}; kw...) =
  map(Multispan, sets(apex(span); kw...),
      unpack_components(legs(span); kw...))
unpack_diagram(cospan::Multicospan{<:ACSet}; kw...) =
  map(Multicospan, sets(apex(cospan); kw...),
      unpack_components(legs(cospan); kw...))
unpack_diagram(para::ParallelMorphisms{<:ACSet}; kw...) =
  map(ParallelMorphisms, unpack_components(hom(para); kw...))
unpack_diagram(comp::ComposableMorphisms{<:ACSet}; kw...) =
  map(ComposableMorphisms, unpack_components(hom(comp); kw...))

function unpack_diagram(diag::Union{FreeDiagram{ACS},BipartiteFreeDiagram{ACS}};
                        S=nothing, Ts=nothing,all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(diag, Ob=X->SetOb(X,c), Hom=α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(diag, Ob=X->VarSet(X,c), Hom=α->α[c]) for c in attrtypes(S)))
  end
  return res 
end
function unpack_diagram(F::Functor{<:FinCat,<:TypeCat{ACS}};
                        S=nothing, Ts=nothing, all::Bool=false, var::Bool=false
                        ) where {ACS <: ACSet}
  res = NamedTuple(c => map(F, X->SetOb(X,c), α->α[c]) for c in objects(S))
  if all || var 
    return merge(res, NamedTuple(c => map(F, X->VarSet(X,c), α->α[c]) for c in attrtypes(S)))
  end 
  return res 
end

""" Vector of C-sets → named tuple of vectors of sets.
"""
function unpack_sets(Xs::AbstractVector{<:ACSet}; S=nothing, Ts=nothing,
                     all::Bool=false, var::Bool=false)
  # XXX: The explicit use of `FinSet` and `TypeSet` is needed here for the
  # nullary case (empty vector) because the Julia compiler cannot infer the
  # return type of the more general `SetOb`.
  fin_sets = NamedTuple(c => map(X->FinSet(X,c), Xs) for c in objects(S))
  if all
    return merge(fin_sets, (d => Vector{TypeSet}(map(X->TypeSet(X,d), Xs)) for d in attrtypes(S)))
  elseif var 
    return merge(fin_sets, map(attrtypes(S)) do d 
      T = VarSet{attrtype_instantiation(S,Ts,d)}
      d => T[T(nparts(X,d)) for X in Xs]
    end)
  else 
    return fin_sets
  end 
end

""" Vector of C-set transformations → named tuple of vectors of functions.
"""
function unpack_components(αs::AbstractVector{<:ACSetMorphism};
    S=nothing, Ts=nothing, all::Bool=false, var::Bool=false)
  res = NamedTuple(c => map(α -> α[c], αs) for c in objects(S))
  if !(all || var) return res end 
  f = var ? identity : type_components
  merge(res, NamedTuple(map(attrtypes(S)) do c 
  c => map(α-> f(α)[c] isa LooseVarFunction ? f(α)[c].loose : f(α)[c], αs)
  end))
end

""" Named tuple of vectors of FinFunctions → vector of C-set transformations.
"""
function pack_components(fs::NamedTuple{names}, doms, codoms;
                         type_components=nothing) where names
  # XXX: Is there a better way?
  components = map((x...) -> NamedTuple{names}(x), fs...)
  if isnothing(type_components) || all(isempty,type_components)
    map(ACSetTransformation, components, doms, codoms)
  else 
    map(LooseACSetTransformation, components, type_components, doms, codoms)
  end
end

""" C-set → named tuple of sets.
"""
function sets(X::ACSet; S=nothing, Ts=nothing, all::Bool=false,var::Bool=false)
  S = isnothing(S) ? acset_schema(X) : S
  Ts = isnothing(Ts) ? datatypes(X) : Ts
  res = NamedTuple(c => SetOb(X,c) for c in objects(S))
  if all 
    return merge(res, NamedTuple(c => SetOb(X,c) for c in attrtypes(S)))
  elseif var 
    return merge(res, NamedTuple(c => VarSet{attrtype_instantiation(S,Ts,c)}(
      nparts(X,c)) for c in attrtypes(S)))
  else 
    return res
  end 
end

end # module
