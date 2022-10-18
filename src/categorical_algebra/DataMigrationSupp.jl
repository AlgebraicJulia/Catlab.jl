module DataMigrationSupp
using ..Categories, ..FinCats, ..Limits, ..Diagrams, ..FinSets, ..CSets
using ..FinCats: FinCatPresentation


"""
Induce a subcategory by picking out some objects and some morphisms. 
Some of the specified morphisms may not be included, if their src/tgt are not
TODO: filter equations by those whose paths are still included.
"""
function sub_cat(C::FinCatGraph, sub_obs, subhoms)
  new_grph = typeof(C.graph)()
  sh = subhoms ∩ vcat(incident(C.graph, sub_obs, :src)...) ∩ vcat(incident(C.graph, sub_obs, :tgt)...)
  new_v, new_e = copy_parts!(new_grph, C.graph; V=sub_obs, E=sh)
  new_cat = FinCat(new_grph)
  return FinFunctor(new_v, new_e, new_cat, C)
end 

function sub_cat(C::FinCatPresentation, sub_obs, sub_homs)
  error("Todo")
end

"""
Invert an injection of FinCats. 
This means we do not have to worry about generators being sent 
to compositions of generators. Nor multiple options to pick from.
For objects in codomain not mapped upon, pick an arbitrary element.
"""
function invert_inj(F::FinFunctor)
  om = Dict(map(ob_generators(codom(F))) do o 
    gs = [g for g in ob_generators(dom(F)) if ob_map(F,g)==o]
    o => isempty(gs) ? first(ob_generators(dom(F))) : only(gs)
  end)
  hm = Dict(map(hom_generators(codom(F))) do o 
    gs = [g for g in hom_generators(dom(F)) if hom_map(F,g)==o]
    o => isempty(gs) ? first(hom_generators(dom(F))) : only(gs)
  end)
  FinFunctor(om, hm, codom(F), dom(F))
end

"""Remove attributes from an ACSet schema presentation"""
de_attr(S::FinCatPresentation{ThSchema}) = FinCat(de_attr(presentation(S)))

function de_attr(S::Presentation)
  new_S, om, hm = Presentation(S.syntax), Dict(), Dict()
  for o in S.generators[:Ob] om[o] = add_generator!(new_S, o) end 
  for h in S.generators[:Hom] hm[h] = add_generator!(new_S, h) end 
  return new_S
end

"""
Remove attributes of codomain of a functor into an ACSet presentation. This
requires removing objects in the domain which map onto attributes
"""
function de_attr(F::FinFunctor{C,D}) where {C,D<:FinCatPresentation{ThSchema}}
  Attr = generators(presentation(codom(F)),:AttrType)
  subobs = Dict([k=>v for (k,v) in pairs(F.ob_map) if v ∉ Attr])
  new_dom = sub_cat(dom(F), collect(keys(subobs)), hom_generators(dom(F)))
  ndF = new_dom ⋅ F 
  return FinFunctor(ndF.ob_map, ndF.hom_map, dom(new_dom), de_attr(codom(F))) => new_dom
end 

de_attr(F::QueryDiagram{T}) where T = QueryDiagram{T}(first(de_attr(F.diagram)), Dict())
de_attr(F::SimpleDiagram{T}) where T = SimpleDiagram{T}(first(de_attr(F.diagram)))

"""
Both dom and codom may be affected from removing attributes from their 
codomains by restricting their shapes (i.e. domains) to values which are 
not mapped to attributes.


no_attr_J ↪ J <-- J' ↩ no_attr_J'
     |       ↘ =>↙       |
     |         C         |
     ⌞---> no_attr_C <---⌟

TODO:
- The diagram map should be restricted to objects in no_attr_J
- This only works if T is op. how to access "dom" and "codom" in a 
  T-agnostic way?
"""
function de_attr(F::DiagramHom{T}) where T 
  (da_dom, inj_dom), (da_cdom, inj_cdom) =  de_attr.(diagram.([dom(F), codom(F)]))
  new_shape_map = inj_cdom ⋅ F.shape_map ⋅ invert_inj(inj_dom) # see TODO #2
  DiagramHom{T}(new_shape_map, components(F.diagram_map), da_dom, da_cdom)
end 

"""F is typically a ConjSchemaMigration, defined in DataMigrations.jl"""
function add_attrs(F, res::FinDomFunctor, colimits, acset_type)
  C = dom(F)
  om = Dict(map(zip(colimits,ob_generators(C))) do (colim, g) 
    c = ob_map(res, g)
    new_c = acset_type()
    copy_parts!(new_c, c)
    # Set attributes if known 
    Fg = ob_map(F, g)
    if Fg isa QueryDiagram 
      FgC = shape(Fg)
      for (attr_ind, attr_val) in collect(Fg.params)
        for h in hom_generators(FgC)
          if codom(FgC, h) == attr_ind
            at_name = Symbol(hom_map(Fg, h)) # e.g. :weight
            dom_ind = dom(FgC, h) 
            part_name = Symbol(ob_map(Fg, dom_ind)) # e.g :E
            new_c_ind = legs(colim)[dom_ind][part_name](1) # map into repr
            set_subpart!(new_c, new_c_ind, at_name, attr_val)
          end
        end
      end
    end 
    return g => new_c
  end)
  hm = Dict(map(hom_generators(C)) do h  
    m = Dict([k => collect(v) for (k,v) in collect(pairs(components(hom_map(res, h))))])
    h => ACSetTransformation(om[codom(C,h)], om[dom(C,h)]; m...)
  end)
  FinDomFunctor(om, hm, C, TypeCat{acset_type, ACSetTransformation}())
end

end # module
