
""" Colimit of attributed C-sets that stores the pointwise colimits in Set.
"""
@struct_hash_equal struct ACSetColimit{Ob <: ACSet, Diagram,
    Cocone <: Multicospan{Ob}, Colimits <: NamedTuple} <: AbstractColimit{Ob,Diagram}
  diagram::Diagram
  cocone::Cocone
  colimits::Colimits
end

⊕(xs::AbstractVector{T}) where {S, T<:StructACSet{S}} = 
  foldl(⊕, xs; init=apex(initial(T)))

initial(::Type{T}; kw...) where T <: ACSet =
  colimit(EmptyDiagram{T}(TightACSetTransformation); kw...)

coproduct(X::ACSet, Y::ACSet; kw...) =
  colimit(ObjectPair(X, Y, TightACSetTransformation); kw...)
  
coproduct(Xs::AbstractVector{<:ACSet}; kw...) =
  colimit(DiscreteDiagram(Xs, TightACSetTransformation); kw...)

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

colimit(::Type{<:Tuple{VarSet,<:Any}}, diagram) = 
  colimit(diagram, ToBipartiteColimit())

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
