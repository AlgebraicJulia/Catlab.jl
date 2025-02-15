module Discrete
export DiscreteDiagram, EmptyDiagram, SingletonDiagram, ObjectPair

using StaticArrays: StaticVector, SVector

using StructEquality

using ..FreeDiagrams
import ..FreeDiagrams: ob

# Discrete diagrams
#------------------

""" Discrete diagram: a diagram with no non-identity morphisms.
"""
@struct_hash_equal struct DiscreteDiagram{Ob,Hom,Obs<:AbstractVector{Ob}} <:
    FixedShapeFreeDiagram{Ob,Hom}
  objects::Obs
end

DiscreteDiagram(objects::Obs, Hom::Type=Any) where {Ob,Obs<:AbstractVector{Ob}} =
  DiscreteDiagram{Ob,Hom,Obs}(objects)

const EmptyDiagram{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{0,Ob}}
const SingletonDiagram{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{1,Ob}}
const ObjectPair{Ob,Hom} = DiscreteDiagram{Ob,Hom,<:StaticVector{2,Ob}}

EmptyDiagram{Ob}(Hom::Type=Any) where Ob = DiscreteDiagram(SVector{0,Ob}(), Hom)
SingletonDiagram(ob, Hom::Type=Any) = DiscreteDiagram(SVector(ob), Hom)
ObjectPair(first, second, Hom::Type=Any) =
  DiscreteDiagram(SVector(first, second), Hom)

ob(d::DiscreteDiagram) = d.objects

Base.iterate(d::DiscreteDiagram, args...) = iterate(d.objects, args...)
Base.eltype(d::DiscreteDiagram) = eltype(d.objects)
Base.length(d::DiscreteDiagram) = length(d.objects)
Base.getindex(d::DiscreteDiagram, i) = d.objects[i]
Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)
Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

end # module