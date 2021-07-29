module CatElements
using Catlab
using ..CSets
using ..FinSets
using ...Present, ...Theories
using ...Theories: Category, CatDesc, AttrDesc, ob, hom, attr, adom, acodom
import Catlab.Present: Presentation

export ThElements, AbstractElements, Elements, elements


@present ThElements(FreeSchema) begin
  (El, Arr, Ob, Hom)::Ob
  Name::Data
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

const AbstractElements = AbstractACSetType(ThElements)
const Elements = ACSetType(ThElements, index=[:src, :tgt, :πₑ, :πₐ])

"""    elements(X::AbstractACSet)

construct the category of elements from an ACSet. This only correctly handles the CSet part.
This transformation converts an instance of C into a Graph homomorphism. The codomain of the
homomorphism is a graph shaped like the schema. This is one half of the isomorphism between
databases and knowledge graphs.
"""
function elements(X::ACS) where
  {CD <: CatDesc, ACS <: AbstractCSet{CD}}
  Y = Elements{Symbol}()

  add_parts!(Y, :Ob, length(ob(CD)), nameo=ob(CD))
  els = map(enumerate(ob(CD))) do (i,c)
    add_parts!(Y, :El, nparts(X, c), πₑ = i)
  end

  add_parts!(Y, :Hom, length(hom(CD)), dom=dom(CD), cod=codom(CD), nameh=hom(CD))
  map(enumerate(zip(hom(CD), dom(CD), codom(CD)))) do (i, trip)
    f, ci, di = trip
    c = ob(CD)[ci]
    d = ob(CD)[di]
    nc = nparts(X, c)
    add_parts!(Y, :Arr, nparts(X, c), src = els[ci], tgt = view(els[di], X[f]), πₐ = i)
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
  obs = Dict{Tuple{Symbol, Int}, Any}()
  for a in 1:nparts(X, :Ob)
    class = X[a, :nameo]
    for (i,j) in enumerate(incident(X, a, :πₑ))
      ob = Ob(FreeSchema, Symbol("$(class)_$i"))
      obs[(class, j)] = ob
    end
  end
  add_generators!(P, values(obs))
  homs = Dict{Tuple{Symbol, Int}, Any}()
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
