module IdFinFunctor

export IdentityFinDomFunctor

using StructEquality
using GATlab

using ...Paths: Path
using ...Categories: Cat, obtype, homtype
using ..FinCats: Cat, ThFinCat, obtype, homtype, FinCat, gentype

using ..FinFunctors: ThFinDomFunctor
import ..FinFunctors: FinDomFunctor, FinFunctor

using .ThFinCat: compose, dom, codom, src, tgt

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFinDomFunctor{O,H,G}
  dom::FinCat
  IdentityFinDomFunctor(c::FinCat) = new{obtype(c), homtype(c), gentype(c)}(c)
end

GATlab.getvalue(i::IdentityFinDomFunctor) = i.dom

function Base.show(io::IO, ::IdentityFinDomFunctor)
  print(io, "id(")
  #show_domains(io, F, codomain=false) #TODO
  print(io, ")")
end

@instance ThFinDomFunctor{O,O,H,H,G,FinCat,FinCat} [
    model::IdentityFinDomFunctor{O,H,G}] where {O,H,G} begin 

  dom()::FinCat = getvalue(model)

  codom()::FinCat = getvalue(model)

  ob_map(x::O)::O = x

  function gen_map(x::G)::H
    C = dom[model]()
    compose(getvalue(model), Path([x], src(C, x), tgt(C,x)))
  end
end

# Convenience constructors
##########################

FinFunctor(c::FinCat) = FinFunctor(IdentityFinDomFunctor(c))

end # module
