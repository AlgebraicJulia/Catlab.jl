""" Data Migration functors
"""
module DataMigration

export Σ, Functor

using ...Theories
using ...Theories: CatDesc, AttrDesc, ob, hom, dom, codom
using ...CSetDataStructures
using ..FinSets, ..CSets, ..Limits, ..FreeDiagrams
using ...Graphs
using ...Present

import ...CategoricalAlgebra.FreeDiagrams: FreeDiagram

""" Functor

A functor ``F: \\mathcal{C} \\to \\mathcal{D}`` consists of a map of objects and a 
map of homomorphisms from a domain category ``\\mathcal{C}``  to a codomain
category ``\\mathcal{D}``.
"""
struct Functor{Schema, Ob, Hom}
  FOb::Dict{Ob, Ob}
  FHom::Dict{Hom, Hom}
  dom::Presentation{Schema, Symbol}
  codom::Presentation{Schema, Symbol}
end

""" Inv(F::Functor)

For a functor ``F: \\mathcal{C} \to \\mathcal{D}``, 
returns a function which when given an object (resp. morphism)
of ``\\mathcal{D}``, returns an array of objects (resp. morphisms) 
of ``\\mathcal{C}`` in the preimage.
"""
function Inv(F::Functor{Schema, Ob, Hom}) where {Schema, Ob, Hom}
  y::Union{Ob, Hom} -> begin
    y isa Ob ? D = F.FOb : D = F.FHom
    [k for (k,v) in D if v == y]
  end
end


""" add_hom!(d::FreeDiagram{Ob, Hom}, src_ob::Ob, tgt_ob::Ob, hom::Hom)

Adds a hom to `d` from the vertex with object `src_ob` to the vertex with object `tgt_ob`.
"""
function add_hom!(d::FreeDiagram, src_ob, tgt_ob, hom) 
  src_idx = first(incident(d, src_ob, :ob))
  tgt_idx = first(incident(d, tgt_ob, :ob))
  return add_edge!(d, src_idx, tgt_idx, hom = hom)
  end

""" FreeDiagram(pres::Presentation{Schema, Symbol})

Returns a `FreeDiagram` whose objects are the generating objects of `pres` and 
whose homs are the generating homs of `pres`.
"""
function FreeDiagram(pres::Presentation{Schema, Symbol}) where {Schema}
  obs = Array{FreeSchema.Ob}(generators(pres, :Ob))
  homs = Array{FreeSchema.Hom}(generators(pres, :Hom))
  doms = map(h -> generator_index(pres, nameof(dom(h))), homs)
  codoms = map(h -> generator_index(pres, nameof(codom(h))), homs)
  return FreeDiagram(obs, collect(zip(homs, doms, codoms)))
end


""" Σ(F::Functor)

which takes a ``\\mathcal{C}``-Set ``X: \\mathcal{C} \\to \\mathsf{Set}`` 
and produces the pushforward ``\\Sigma_F(X): \\mathcal{D} \\to \\mathsf{Set}``.

``\\mathcal{D}`` must be a free schema with no cycles. 
"""
function Σ(F::Functor{Schema, Ob, Hom}) where {Schema, Ob, Hom}
  diagramC = FreeDiagram(F.dom)
  diagramD = FreeDiagram(F.codom)
  FInv = Inv(F)

  comma_cats = FreeDiagram{FreeDiagram, ACSetTransformation}()
  add_vertices!(comma_cats,
    nparts(diagramD, :V), 
    ob = map( _ ->  FreeDiagram{Pair{Ob, Hom}, Hom}(), parts(diagramD, :V))
  )

  for d in topological_sort(diagramD)
    F∇d = ob(comma_cats, d)
    id_d = id(ob(diagramD, d))

    # If FOb[c] = d, add an objects (c, id(d)) to F∇d
    preimage_d = FInv(ob(diagramD, d)) 
    id_obs = add_vertices!(F∇d, length(preimage_d), ob = map(c->c=>id_d, preimage_d))
    
    # if FHom[h] = id(d), add a hom h: (dom(h), id(d)) -> (codom(h), id(d)) to F∇d 
    id_homs = map(FInv(id_d)) do h
      add_hom!(F∇d, dom(h) => id_d, codom(h) => id_d, h)
    end
    # for g: d' -> d in D (note that F∇d' must have already been constructed)
    for g in incident(diagramD, d, :tgt)
      d′ = src(diagramD, g)
      F∇d′ = ob(comma_cats, d′)

      # for (c,f) in F∇d' add ob (c, compose(f,g)) to F∇d
      vs = add_vertices!(F∇d, nparts(F∇d′, :V), ob = map(ob(F∇d′)) do (c,f)
          c => compose(f, hom(diagramD, g))                
        end)
    
      # for h: (c, f) -> (c', f') in diagram_d', add hom h to F∇d    
      es = add_edges!(F∇d, vs[src(F∇d′)], vs[tgt(F∇d′)], hom = hom(F∇d′))

      # g induces an inclusion F∇d′ to F∇d 
      add_edge!(comma_cats, d′, d, hom = ACSetTransformation((V = collect(vs), E = collect(es)), F∇d′, F∇d))

      # for every (c,f) in the recently added objects. If FHom[h] == f, then add the hom 
      #       h: (c,f) -> (codom(h), idv)
      # relies on D being free
      for (c, f) in ob(F∇d, vs)
        for h in FInv(f)
          dom(h) == c && add_hom!(F∇d, c => f, codom(h) => id_d, h)
        end
      end
    end 
  end # end of populating comma_cats 

  function pushforward(X::ACSet) 
    Presentation(X) == F.dom || error("X has the wrong Schema")

    Y = ACSetType(F.codom)()

    colimX = map(parts(diagramD, :V)) do i
      F∇d = ob(comma_cats, i)
      Xobs = map(ob(F∇d)) do (c,_)
        FinSet(nparts(X, nameof(c)))
      end
      Xhoms = map(parts(F∇d, :E)) do g
        FinFunction(X[nameof(hom(F∇d, g))], Xobs[src(F∇d, g)], Xobs[tgt(F∇d, g)])
      end
      colimit(FreeDiagram(Xobs, collect(zip(Xhoms, src(F∇d), tgt(F∇d)))))
    end

    for d in parts(diagramD, :V)
      add_parts!(Y, nameof(ob(diagramD, d)), length(apex(colimX[d])))
    end
    
    for g in parts(diagramD, :E)
      if nparts(Y, nameof(dom(hom(diagramD, g)))) == 0
        continue
      end
      set_subpart!(Y, nameof(hom(diagramD, g)),
        universal(colimX[src(diagramD, g)], 
          Multicospan(legs(colimX[tgt(diagramD, g)])[hom(comma_cats, g)[:V].func])
        ).func
      )
    end
    return Y
  end
end

end #module
