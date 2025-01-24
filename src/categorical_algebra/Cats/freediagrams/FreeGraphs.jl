module FreeGraphs 
export FreeDiagram, SchFreeDiagram

using StructEquality
using ACSets, GATlab

using .....Graphs
using ...FinCats, ...Functors
import ...FinFunctors: FinDomFunctor, collect_ob, collect_hom

using ..FreeDiagrams
import ..FreeDiagrams: ob, hom, dom, codom, cone_objects, cocone_objects, diagram_type


# Free diagrams
#--------------

@present SchFreeDiagram <: SchGraph begin
  Ob::AttrType
  Hom::AttrType
  ob::Attr(V,Ob)
  hom::Attr(E,Hom)
end

@abstract_acset_type AbstractFreeDiagram <: AbstractGraph

@acset_type FreeDiagram(SchFreeDiagram, index=[:src,:tgt]) <:
  AbstractFreeDiagram

ob(d::AbstractFreeDiagram, args...) = subpart(d, args..., :ob)
hom(d::AbstractFreeDiagram, args...) = subpart(d, args..., :hom)

diagram_type(::AbstractFreeDiagram{S,T}) where {S,T<:Tuple} = T

FreeDiagram(obs::AbstractVector{Ob},
            homs::AbstractVector{Tuple{Hom,Int,Int}}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(obs, homs)

function FreeDiagram{Ob,Hom}(obs::AbstractVector,
                             homs::AbstractVector) where {Ob,Hom}
  @assert all(obs[s] == dom(f) && obs[t] == codom(f) for (f,s,t) in homs)
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(obs), ob=obs)
  length(homs) > 0 && add_edges!(d, getindex.(homs,2), getindex.(homs,3), hom=first.(homs))
  return d
end

FreeDiagram(d::FixedShapeFreeDiagram{Ob,Hom}; kw...) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(d; kw...)

function FreeDiagram{Ob,Hom}(discrete::DiscreteDiagram) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, length(discrete), ob=collect(discrete))
  return d
end

function FreeDiagram{Ob,Hom}(span::Multispan) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  v₀ = add_vertex!(d, ob=apex(span))
  vs = add_vertices!(d, length(span), ob=feet(span))
  add_edges!(d, fill(v₀, length(span)), vs, hom=legs(span))
  return d
end

function FreeDiagram{Ob,Hom}(cospan::Multicospan) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs = add_vertices!(d, length(cospan), ob=feet(cospan))
  v₀ = add_vertex!(d, ob=apex(cospan))
  add_edges!(d, vs, fill(v₀, length(cospan)), hom=legs(cospan))
  return d
end

function FreeDiagram{Ob,Hom}(para::ParallelMorphisms) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  add_vertices!(d, 2, ob=[dom(para), codom(para)])
  add_edges!(d, fill(1,length(para)), fill(2,length(para)), hom=hom(para))
  return d
end

function FreeDiagram{Ob,Hom}(comp::ComposableMorphisms) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  n = length(comp)
  add_vertices!(d, n+1, ob=[dom.(comp); codom(comp)])
  add_edges!(d, 1:n, 2:(n+1), hom=hom(comp))
  return d
end

function FreeDiagram{Ob,Hom}(diagram::BipartiteFreeDiagram) where {Ob,Hom}
  d = FreeDiagram{Ob,Hom}()
  vs₁ = add_vertices!(d, nv₁(diagram), ob=ob₁(diagram))
  vs₂ = add_vertices!(d, nv₂(diagram), ob=ob₂(diagram))
  add_edges!(d, vs₁[src(diagram)], vs₂[tgt(diagram)], hom=hom(diagram))
  return d
end
FreeDiagram(diagram::BipartiteFreeDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(diagram)

function FreeDiagram{Ob,Hom}(F::Functor{<:FinCat{Int}}) where {Ob,Hom}
  J = dom(F)
  js = ob_generators(J)
  js == 1:length(js) || error("Objects must be numbers 1:n")

  diagram = FreeDiagram{Ob,Hom}()
  add_vertices!(diagram, length(js), ob=[ob_map(F,j) for j in js])
  for f in hom_generators(J)
    add_edge!(diagram, dom(J,f), codom(J,f), hom=hom_map(F,f))
  end
  diagram
end
FreeDiagram(F::Functor{<:FinCat{Int},<:Cat{Ob,Hom}}) where {Ob,Hom} =
  FreeDiagram{Ob,Hom}(F)

(::Type{BFD})(diagram::FreeDiagram; kw...) where BFD <: BipartiteFreeDiagram =
  BFD(FinDomFunctor(diagram); kw...)

# FinDomFunctors as diagrams
#---------------------------

diagram_type(F::FinDomFunctor{Dom,Codom}) where {Ob,Hom,Dom,Codom<:Cat{Ob,Hom}} =
  Tuple{Ob,Hom}
cone_objects(F::FinDomFunctor) = collect_ob(F)
cocone_objects(F::FinDomFunctor) = collect_ob(F)

""" Wrapper type to interpret `FreeDiagram` as a `FinDomFunctor`.
"""
@struct_hash_equal struct FreeDiagramFunctor{Ob,Hom,Codom} <:
    FinDomFunctor{FreeCatGraph{FreeDiagram{Ob,Hom}},Codom}
  diagram::FreeDiagram{Ob,Hom}
  codom::Codom
end
FinDomFunctor(diagram::FreeDiagram, codom::Cat) =
  FreeDiagramFunctor(diagram, codom)
FinDomFunctor(diagram::FreeDiagram{Ob,Hom}) where {Ob,Hom} =
  FreeDiagramFunctor(diagram, TypeCat(Ob, Hom))

dom(F::FreeDiagramFunctor) = FreeCatGraph(F.diagram)

Functors.do_ob_map(F::FreeDiagramFunctor, x) = ob(F.diagram, x)
Functors.do_hom_map(F::FreeDiagramFunctor, f) = hom(F.diagram, f)

collect_ob(F::FreeDiagramFunctor) = ob(F.diagram)
collect_hom(F::FreeDiagramFunctor) = hom(F.diagram)

end # module
