""" Formerly called FreeGraph """
module FreeGraphs
export FreeGraph

using GATlab, ACSets

using .....Theories: ThCategory
using .....Graphs
using .....BasicSets: FinSet
using ...FreeDiagrams: FreeDiagram, ThFreeDiagram, obtype, homtype, obset, homset
import ...FreeDiagrams: fmap

using .ThFreeDiagram

@present SchFreeGraph <: SchGraph begin
  (Ob, Hom)::AttrType
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

@abstract_acset_type AbstractFreeGraph <: AbstractGraph

@acset_type FreeGraph(SchFreeGraph, index=[:src,:tgt]) <: AbstractFreeGraph

""" Infer types """
FreeGraph(obs::AbstractVector{Ob},homs::AbstractVector{Tuple{Hom,Int,Int}}; cat=nothing
           ) where {Ob,Hom} = FreeGraph{Ob,Hom}(obs, homs; cat)

function FreeGraph{Ob,Hom}(obs::AbstractVector,
                             homs::AbstractVector; cat=nothing) where {Ob,Hom}
  cat = isnothing(cat) ? Dispatch(ThCategory, [Ob,Hom]) : cat
  for (f,s,t) in homs
    obs[s] == dom[cat](f) || error("Bad dom($f) = $(dom[cat](f)) ≠ $(obs[s])")
    obs[t] == codom[cat](f) || error("Bad codom($f) = $(codom[cat](f)) ≠ $(obs[t])")
  end
  d = FreeGraph{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  length(homs) > 0 && add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

FreeGraph(f::FreeGraph) = f

function FreeGraph(d::FreeDiagram)
  F = FreeGraph{obtype(d), homtype(d)}()
  # In case ob set isn't FinSetInt, get a mapping from V elements to int
  vlookup = Dict()
  for (i,v) in enumerate(obset(d))
    vlookup[v] = i 
    add_vertex!(F; ob=obmap(d, v))
  end
  for e in homset(d)
    add_edge!(F, vlookup[src(d, e)], vlookup[tgt(d, e)]; hom=hommap(d, e))
  end
  return F
end

# Constructor
#############
FreeCatGraph(n::FreeGraph) =  FreeCatGraph(getvalue(n))

# FreeDiagraminterface 
######################

@instance ThFreeDiagram{Int,Int,Ob,Hom,FinSet
                       } [model::FreeGraph{Ob,Hom}] where {Ob,Hom} begin
  src(x::Int)::Int = src(model, x)
  tgt(x::Int)::Int = tgt(model, x)
  obmap(x::Int)::Ob = model[x, :ob]
  hommap(x::Int)::Hom = model[x, :hom]
  obset()::FinSet = FinSet(nv(model))
  homset()::FinSet = FinSet(ne(model))
end

end # module