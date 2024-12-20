module Discrete 
export EmptyDiagram, SingletonDiagram, ObjectPair, DiscreteDiagram

using StructEquality
using StaticArrays: StaticVector, SVector

using GATlab 
import ACSets: objects

using .....BasicSets: FinSet
using ...FreeDiagrams: ThFreeDiagram
import ...FreeDiagrams: fmap, cone_objects, cocone_objects

""" Discrete diagram: a diagram with no non-identity morphisms.
"""
@struct_hash_equal struct DiscreteDiagram{Ob,Obs<:AbstractVector{Ob}}
  objects::Obs
end

DiscreteDiagram{Ob}(o::Obs) where {Ob,Obs<:AbstractVector{Ob}} = 
  DiscreteDiagram{Ob,Obs}(o)

GATlab.getvalue(d::DiscreteDiagram) = d.objects

cone_objects(d::DiscreteDiagram) = d.objects

cocone_objects(d::DiscreteDiagram) = d.objects

objects(d::DiscreteDiagram) = d.objects

Base.length(m::DiscreteDiagram) = length(m.objects) 

Base.iterate(m::DiscreteDiagram, x...) = iterate(m.objects, x...)

Base.eltype(d::DiscreteDiagram) = eltype(d.objects)

Base.getindex(d::DiscreteDiagram, i) = d.objects[i]

Base.firstindex(d::DiscreteDiagram) = firstindex(d.objects)

Base.lastindex(d::DiscreteDiagram) = lastindex(d.objects)

@instance ThFreeDiagram{Int,Int,Ob,Union{},FinSet
                       } [model::DiscreteDiagram{Ob}] where {Ob} begin
  src(::Int)::Int = error("No edges")
  tgt(::Int)::Int = error("No edges")
  obmap(x::Int)::Ob = model[x]
  hommap(::Int)::Union{} = error("No edges")
  obset()::FinSet = FinSet(length(model))
  homset()::FinSet = FinSet(0)
end

""" Apply ob map to the objects of a discrete diagram """
fmap(d::DiscreteDiagram, o, _) = DiscreteDiagram(o.(d))  

# Special subtypes
#-----------------

const EmptyDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{0,Ob}}

EmptyDiagram{Ob}() where Ob = DiscreteDiagram(SVector{0,Ob}())

EmptyDiagram() = EmptyDiagram{Union{}}()

const SingletonDiagram{Ob} = DiscreteDiagram{Ob,<:StaticVector{1,Ob}}

SingletonDiagram(ob) = DiscreteDiagram(SVector(ob))

const ObjectPair{Ob} = DiscreteDiagram{Ob,<:StaticVector{2,Ob}}

ObjectPair(first, second) = DiscreteDiagram(SVector(first, second))


end # module