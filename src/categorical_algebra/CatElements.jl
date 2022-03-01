module CatElements
export ThElements, AbstractElements, Elements, elements, inverse_elements

using DataStructures: OrderedDict

using ..CSets, ..FinSets
using ...Present, ...Theories
using ...Theories: Category, ob, hom, dom_nums, codom_nums

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
    c = obs[ci]
    add_parts!(Y, :Arr, nparts(X, c), src=els[ci], tgt=view(els[di], X[f]), πₐ=i)
  end
  return Y
end


"""    elements(f::ACSetTransformation)

Apply category of elements functor to a morphism f: X->Y.
This relies on the fact `elements` of an object puts El components from the same
Ob in a contiguous index range.
"""
function elements(f::ACSetTransformation{S}) where S
  X, Y = elements.([dom(f), codom(f)])

  # Apply offset to homomorphism data
  offs = map((parts(X, :Ob))) do i
    off=findfirst(==(i), Y[:πₑ])
    isnothing(off) ? 0 : off-1
  end
  pts = vcat([collect(f[o]).+off for (o, off) in zip(ob(S), offs)]...)
  # *strict* ACSet transformation uniquely determined by its action on vertices
  return only(homomorphisms(X, Y; initial=Dict([:El=>pts])))
end


"""    inverse_elements(X::AbstractElements, typ::StructACSet)
Compute inverse grothendieck transformation on the result of `elements`.
Does not assume that the elements are ordered.
Rather than dynamically create a new ACSet type, it requires any instance of
the ACSet type that it's going to try to create

If the typed graph tries to assert conflicting values for a foreign key, fail.
If no value is specified for a foreign key, the result will have 0's.
"""
function inverse_elements(X::AbstractElements, typ::StructACSet)
  res = typeof(typ)()
  o_ids = ob_ids(X)
  for (o, is) in pairs(o_ids)
    add_parts!(res, o, length(is))
  end
  cols = [[:πₐ,:nameh], :src, :tgt, [:src,:πₑ, :nameo], [:tgt, :πₑ, :nameo]]
  for (h, s, t, so, to) in zip([X[col] for col in cols]...)
    src_ind, tgt_ind = o_ids[so][s], o_ids[to][t]
    err = "Not a discrete opfibration: $h: $so#$s sent to multiple values"
    res[src_ind, h] == 0 || error(err)
    set_subpart!(res, src_ind, h, tgt_ind)
  end
  return res
end

"""
Determine the (partial) mapping from Elements to indices for each component
E.g. [V,E,V,V,E] ⟶ [V=>{1↦1, 3↦2, 4↦3}, E=>{2↦1, 5↦2}]
"""
function ob_ids(X::AbstractElements)
  obs = Dict([o => findall(i -> X[i,[:πₑ,:nameo]] == o, parts(X,:El))
              for o in X[:nameo]])
  return Dict([o => Dict(v=>i for (i,v) in enumerate(is)) for (o, is) in obs])
end

"""    inverse_elements(X::AbstractElements, typ::StructACSet)

Compute inverse grothendieck transformation on a morphism of Elements
"""
function inverse_elements(f::ACSetTransformation, typ::StructACSet)
  iX, iY = [inverse_elements(x, typ) for x in [dom(f), codom(f)]]
  oX, oY = ob_ids.([dom(f), codom(f)])
  comps = map(dom(f)[:nameo]) do ob
    offY = oY[ob]
    x_ids = sort(collect(keys(oX[ob])))
    ob => [offY[f[:El](xi)] for xi in x_ids]
  end
  return ACSetTransformation(iX, iY; Dict(comps)...)
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
end
