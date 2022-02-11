module CatElements
export ThElements, AbstractElements, Elements, elements, attr_elements

using DataStructures: OrderedDict

using ..CSets, ..FinSets
using ...Present, ...Theories
using ...Theories: Category, ob, hom, dom_nums, codom_nums,
                   attr, attrtype, adom_nums, acodom_nums

@present ThElements(FreeSchema) begin
  (El, Arr, Ob, Hom)::Ob
  Name::AttrType
  src::Hom(Arr, El)
  tgt::Hom(Arr, El)
  dom::Hom(Hom, Ob)
  cod::Hom(Hom, Ob)
  πₑ::Hom(El, Ob)
  πₐ::Hom(Arr, Hom)
  nameo::Attr(Ob, Name)
  nameh::Attr(Hom, Name)

  src⋅πₑ == πₐ⋅dom
  tgt⋅πₑ == πₐ⋅cod
end

@abstract_acset_type AbstractElements
@acset_type Elements(ThElements, index=[:src, :tgt, :πₑ, :πₐ]) <: AbstractElements

"""    elements(X::AbstractACSet)

construct the category of elements from an ACSet. This only correctly handles the CSet part.
This transformation converts an instance of C into a Graph homomorphism. The codomain of the
homomorphism is a graph shaped like the schema. This is one half of the isomorphism between
databases and knowledge graphs.
"""
function elements(X::StructACSet{S}) where S
  Y = Elements{Symbol}()

  obs = ob(S)
  add_parts!(Y, :Ob, length(obs), nameo=obs)
  els = map(enumerate(obs)) do (i,c)
    add_parts!(Y, :El, nparts(X, c), πₑ = i)
  end

  add_parts!(Y, :Hom, length(hom(S)), dom=dom_nums(S), cod=codom_nums(S), nameh=hom(S))
  map(enumerate(zip(hom(S), dom_nums(S), codom_nums(S)))) do (i, (f, ci, di))
    c, d = obs[ci], obs[di]
    nc = nparts(X, c)
    add_parts!(Y, :Arr, nparts(X, c), src=els[ci], tgt=view(els[di], X[f]), πₐ=i)
  end
  return Y
end

"""    presentation(X::AbstractElements)

convert a category of elements into a new schema. This is useful for generating large schemas
that are defined as the category of elements of a specified C-Set. For example, the schema for
Bipartite Graphs is the category of elements of the graph with 2 vertices and 1 edge. The 2 vertices
will get mapped to elements `V_1, V_2` and the one edge will be `E_1` and the source and target maps
will be mapped to `src_E_1, tgt_E_1`.
"""
function presentation(X::AbstractElements)
  P = Presentation(FreeSchema)
  obs = OrderedDict{Tuple{Symbol, Int}, Any}()
  for a in 1:nparts(X, :Ob)
    class = X[a, :nameo]
    for (i,j) in enumerate(incident(X, a, :πₑ))
      ob = Ob(FreeSchema, Symbol("$(class)_$i"))
      obs[(class, j)] = ob
    end
  end
  add_generators!(P, values(obs))
  homs = OrderedDict{Tuple{Symbol, Int}, Any}()
  for f in 1:nparts(X, :Hom)
    class = X[f, :nameh]
    for (i,j) in enumerate(incident(X, f, :πₐ))
      domkey = (X[j, [:src, :πₑ, :nameo]], X[j, :src])
      dom = obs[domkey]
      codkey = (X[j, [:tgt, :πₑ, :nameo]], X[j, :tgt])
      codom = obs[codkey]
      homs[(class, j)] = Hom(Symbol("$(class)_$dom"), dom, codom)
    end
  end
  add_generators!(P, values(homs))
  return P, obs, homs
end

@present ThAttrElements <: ThElements begin
  (Item, ItArr, AttrType, Attr)::Ob
  Type::AttrType
  Data::AttrType

  itsrc::Hom(ItArr, El)
  ittgt::Hom(ItArr, Item)
  atsrc::Hom(Attr, Ob)
  attgt::Hom(Attr, AttrType)

  πᵢ::Hom(Item, AttrType)
  πᵢₐ::Hom(ItArr, Attr)

  namea::Attr(Attr, Name)
  nameat::Attr(AttrType, Name)
  type::Attr(AttrType, Type)
  data::Attr(Item, Data)
end

@abstract_acset_type AbstractAttributedElements
@acset_type AttrElements(ThAttrElements, index=[:src, :tgt, :πₑ, :πₐ,
                                            :itsrc, :ittgt, :πᵢ, :πᵢₐ]) <: AbstractAttributedElements


function el_inds(X::StructACSet{S}) where S
  i = 1
  inds = Vector{UnitRange{Int}}()
  for o in ob(S)
    push!(inds, i:(i+nparts(X,o) - 1))
    i += nparts(X,o)
  end
  inds
end

function attr_elements(X::StructACSet{S, Ts}) where {S, Ts}
  Y = AttrElements{Symbol, Type, Any}()
  Y′ = elements(X)
  copy_parts!(Y, Y′)
  attrtypes = attrtype(S)
  types = Ts.parameters

  add_parts!(Y, :AttrType, length(attrtypes), nameat = attrtypes,  type=types)

  attrs = attr(S)
  add_parts!(Y, :Attr, length(attrs), atsrc=adom_nums(S), attgt=acodom_nums(S), namea=attrs)

  els = el_inds(X)
  map(enumerate(zip(attrs, adom_nums(S), acodom_nums(S)))) do (i, (f, oi, ai))
    o = ob(S)[oi]
    items = add_parts!(Y, :Item, nparts(X,o), πᵢ = ai, data = X[f])
    add_parts!(Y, :ItArr, nparts(X,o), itsrc=els[oi], ittgt=items, πᵢₐ=i)
  end
  Y
end

"""    presentation(X::AbstractAttributedElements)

convert a category of elements with attributes into a new schema. Currently
this is performed by simply extending the current attributes to the new
objects.

TODO:
If attributes are going to be treated as homomorphisms, this should check
for unique attributes and generate a new AttrType for each one.
"""
function presentation(X::AbstractAttributedElements)
  X′ = Elements{Symbol}()
  copy_parts!(X′, X)
  P, obs, homs = presentation(X′)
  add_generators!(P, [AttrType(FreeSchema.AttrType, X[at, :nameat]) for at in parts(X, :AttrType)])

  attrs = OrderedDict{Tuple{Symbol, Int}, Any}()
  for a in 1:nparts(X, :Attr)
    o = X[a, :atsrc]
    class = X[o, :nameo]
    for (i,j) in enumerate(incident(X, o, :πₑ))
      oname = Symbol("$(class)_$i")
      cur_attr = Attr(Symbol(X[a, :namea], "_", oname), P[oname], P[X[X[a, :attgt], :nameat]])
      attrs[(class, j)] = cur_attr
    end
  end
  add_generators!(P, values(attrs))
  return P, obs, homs
end
end