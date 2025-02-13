""" This depends on FinSets, so must come afterwards """
module DiscreteFinCats 

export DiscreteFinCat

using StructEquality
using GATlab

import .....Graphs: Graph
using .....BasicSets 
using ...Paths: Path
using ..FinCats: ThFinCat, src
import ..FinCats: FinCat

""" Discrete category on a finite set.

The only morphisms in a discrete category are the identities, which are here
identified with the objects.
"""
@struct_hash_equal struct DiscreteFinCat{Ob}
  set::FinSet
  DiscreteFinCat(s::FinSet) =new{eltype(s)}(s)
end

GATlab.getvalue(D::DiscreteFinCat) = D.set

DiscreteFinCat(n::Integer) = DiscreteFinCat(FinSet(n))

Base.show(io::IO, C::DiscreteFinCat) = print(io, "FinCat($(length(C.set)))")

@instance ThFinCat{Ob,Ob,Union{},Path{Ob,Union{}},FinSet
                  } [model::DiscreteFinCat{Ob}] where {Ob} begin

  Ob(x::Ob) = x ∈ model.set ? x : error("$x not an object of $model")

  Hom(x::Ob, ::Ob, ::Ob) = x ∈ model.set ? x : error("$x not an object of $model")

  id(x::Ob) = x 

  dom(x::Ob) = x 

  codom(x::Ob) = x 

  ob_set() = model.set 

  gen_set() = FinSet(EmptySet())

  decompose(x::Ob) = Path{Int}(x,Union{})

  function compose(x::Path{Ob,Union{}})
    isempty(x) || error("Discrete Cat has only empty ")
    src(x)
  end
  
end

Graph(C::DiscreteFinCat) = if getvalue(getvalue(C)) isa FinSetInt 
  Graph(length(C.set))
else 
  error("Cannot cast $C to a graph")
end

FinCat(s::FinSet) = FinCat(DiscreteFinCat(s))

FinCat(s::Int) = FinCat(DiscreteFinCat(s))

end # module
