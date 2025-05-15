module IdFinFunctor

export IdentityFinDomFunctor

using StructEquality
using GATlab

using ...Paths: Path
using ...Categories: Cat, obtype, homtype
using ..FinCats: Cat, ThFinCat, obtype, homtype, FinCat, gentype, to_hom

using ..FinFunctors: ThFinDomFunctor, to_hom
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
  #show_domains(io, F, codomain=false) #KBTODO
  print(io, ")")
end

@instance ThFinDomFunctor{O,O,H,H,FinCat,FinCat,G} [
    model::IdentityFinDomFunctor{O,H,G}] where {O,H,G} begin 

  dom()::FinCat = getvalue(model)

  codom()::FinCat = getvalue(model)

  ob_map(x::O)::O = x

  hom_map(x::H)::H = x

  gen_map(x::G)::H = to_hom(dom[model](), x)
end

# Convenience constructors
##########################

FinFunctor(c::FinCat) = FinFunctor(IdentityFinDomFunctor(c))

end # module
