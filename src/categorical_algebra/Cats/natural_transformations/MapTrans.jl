module MapTrans 

export FinTransformationMap
using StructEquality
using GATlab

using ...Cats
using ..Transformations
import ..Transformations: Transformation, components
import ..Cats: force


# Mapping-based transformations
#------------------------------

""" Natural transformation with components given by explicit mapping.

A natural transformation α: F → G, where F and G are functors 𝒞 → 𝒟, is an 
assignment for each object X ∈ Ob(𝒞) a morphisms in Hom𝒟(F(x),G(x)) such that,
for all f: X → Y in 𝒞, the diagram commutes:

```
    F                       αₓ
   --↘                 F(X) ⟶ G(X)
𝒞  ⇓α  𝒟            F(f) ↓      ↓ G(f)
   --↗                 F(Y) ⟶ G(Y)
    G                       αᵧ       
```
"""
@struct_hash_equal struct FinTransformationMap{DO, CH, Func<:AbsFunctor}
  components::Union{AbstractVector,AbstractDict}
  dom::FinDomFunctor
  codom::Func
  function FinTransformationMap(comps, F::FinDomFunctor, G::Fun; check=true
                               ) where {Fun<:AbsFunctor}
    O, H = impl_type.([F,F], [:DomOb,:CodomHom])
    C, D = check_transformation_domains(F, G)
    DO = impl_type(C, :Ob)
    DO == O || error("Bad F dom ob type $DO ≠ $O")
    length(comps) == length(ob_generators(C)) ||
      error("Incorrect number of components in $comps for domain category $C")
    if check 
      for o in ob_generators(C)
        comps[o] ∈ hom_set(D) || error("Bad hom $o ↦ $(comps[o]) ∉ $(hom_set(D))")
      end
    end
    new{O,H,Fun}(comps, F, G)
  end
end

@instance ThTransformation{DO, CH, FinDomFunctor, F
                          } [model::FinTransformationMap{DO,CH,F} 
                            ] where {DO,CH,F} begin

  dom()::FinDomFunctor = model.dom

  codom()::F = model.codom

  component(x::DO)::CH = model.components[x]
end 

Transformation(components::Union{AbstractVector,AbstractDict}, 
               F::FinDomFunctor, G::AbsFunctor) =
  Transformation(FinTransformationMap(components, F, G)) |> validate


component(α::FinTransformationMap, x) = α.components[ob_key(dom_ob(α), x)]
components(α::FinTransformationMap) = α.components

op(α::FinTransformationMap) = FinTransformationMap(components(α),
                                                   op(codom(α)), op(dom(α)))
function Base.show(io::IO, α::FinTransformationMap)
  print(io, "FinTransformation(")
  show(io, components(α))
  print(io, ", ")
  # Categories.show_domains(io, α, recurse=false) # KBTODO
  print(io, ", ")
  # Categories.show_domains(io, dom(α))
  print(io, ")")
end

force(α::Transformation) = Transformation(force(getvalue(α)))

force(α::FinTransformationMap) =
   FinTransformationMap(Dict(k => force(v) for (k,v) in components(α)), 
                        force(α.dom), force(α.codom))

end # module
