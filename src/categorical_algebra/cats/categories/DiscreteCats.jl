""" This depends on FinSets, so must come afterwards """
module DiscreteCats 

export DiscreteCat

using StructEquality
using GATlab

using .....BasicSets 
using ..Categories: ThCategoryExplicitSets
import ..Categories: Category

""" Discrete category on a finite set.

The only morphisms in a discrete category are the identities, which are here
identified with the objects.
"""
@struct_hash_equal struct DiscreteCat{Ob}
  set::SetOb
  DiscreteCat(s::SetOb) =new{eltype(s)}(s)
end

GATlab.getvalue(d::DiscreteCat) = d.set

DiscreteCat(n::Integer) = DiscreteCat(FinSet(n))

Base.show(io::IO, C::DiscreteCat) = print(io, "DiscreteCat($(C.set))")

@instance ThCategoryExplicitSets{Ob,Ob} [model::DiscreteCat{Ob}] where {Ob} begin
  Ob(x::Ob) = x ∈ model.set ? x : error("$x not an object of $model")
  Hom(x::Ob, ::Ob, ::Ob) = x ∈ model.set ? x : error("$x not an object of $model")
  id(x::Ob) = x 
  dom(x::Ob) = x 
  codom(x::Ob) = x 
  ob_set() = model.set 
  hom_set() = model.set
  function compose(x::Ob,y::Ob)
    x == y || error("Discrete Cat cannot compose $x $y ")
    return x
  end
end

Graph(C::DiscreteCat) = if getvalue(getvalue(C)) isa FinSetInt 
  Graph(length(C.set))
else 
  error("Cannot cast $C to a graph")
end

Category(s::SetOb) = Category(DiscreteCat(s))

end # module
