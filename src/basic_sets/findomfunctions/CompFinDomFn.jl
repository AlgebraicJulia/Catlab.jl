module CompFinDomFn 

export CompositeFinDomFunction

using StructEquality

using GATlab

using ...BasicSets
using ..FinDomFunctions
import ..FinDomFunctions: ThFinDomFunction, is_indexed, FinDomFunction′
using ..IdFinFunction: IdentityFinFunction

""" Composite of heteromorphisms between **FinSet** and **Set**.

Not to be confused with `Base.ComposedFunctions` for ordinary Julia functions.
"""
@struct_hash_equal struct CompositeFinDomFunction{D,C}
  fst::FinFunction
  mid::FinDomFunction
  snd::SetFunction
  CompositeFinDomFunction(fst::FinFunction, mid::FinDomFunction, snd::SetFunction) = 
    new{impl_type(fst,:Dom), impl_type(snd, :Cod)}(fst, mid, snd)
end

Base.first(f::CompositeFinDomFunction) = f.fst
GATlab.getvalue(f::CompositeFinDomFunction) = f.mid
Base.last(f::CompositeFinDomFunction) = f.snd

is_indexed(f::CompositeFinDomFunction) = is_indexed(first(f)) || is_indexed(last(f))

function Base.show(io::IO, f::CompositeFinDomFunction)
  print(io, "compose(")
  show(io, first(f))
  print(io, ", ")
  show(io, last(f))
  print(io, ")")
end

# FinFunction implementation 
############################

@instance ThFinDomFunction{D,C} [model::CompositeFinDomFunction{D,C}] where {D,C} begin

  dom()::FinSet = dom(first(model))
  
  codom()::SetOb = codom(last(model))

  app(i::D)::C = last(model)(getvalue(model)(first(model)(i)))
  # precompose(f::FinFunction)::FinDomFunction′ = FinDomFunction(f, model)
  # Create a (biased) nested composite function using constructor below
  postcompose(f::SetFunction)::FinDomFunction′ = FinDomFunction(model, f) 
end


# Default FinFunction constructor
#################################

""" Assume codom(f) ⊆ dom(g) """
function FinDomFunction(f::FinFunction, g::SetFunction)
  FinDomFunction(CompositeFinDomFunction(f,FinDomFunction(codom(f), dom(g)), g))
end

function FinDomFunction(f::FinFunction, g::FinDomFunction,)
  getvalue(f) isa IdentityFinFunction && return g
  vg = getvalue(g)
  vg isa CompositeFinDomFunction && return FinDomFunction(CompositeFinDomFunction(FinFunction(f, first(vg)), getvalue(vg), last(vg)))
  FinDomFunction(CompositeFinDomFunction(f,g, SetFunction(codom(g))))
end

function FinDomFunction(f::FinDomFunction, g::SetFunction)
  getvalue(g) isa IdentityFunction && return f
  vf = getvalue(f)
  vf isa CompositeFinDomFunction && return FinDomFunction(CompositeFinDomFunction(first(vf), getvalue(vf), SetFunction(last(vf), g)))
  FinDomFunction(CompositeFinDomFunction(FinFunction(dom(f)),f, g))
end

end # module
