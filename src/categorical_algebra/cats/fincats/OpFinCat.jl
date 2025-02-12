module OpFinCat 

export OppositeFinCat

using StructEquality

using GATlab 
import GATlab: getvalue, equations

using ......BasicSets: FinSet
using ...Paths: Path
using ...Categories: obtype, homtype, ob_set, hom_set
import ...Categories: op
using ..FinCats: ThFinCat, gentype, gen_set, src, tgt
import ..FinCats: FinCat

using .ThFinCat

# Opposite FinCats
##################

@struct_hash_equal struct OppositeFinCat{Ob,Hom,Gen}
  val::FinCat
  OppositeFinCat(f::FinCat) = new{obtype(f), homtype(f), gentype(f)}(f)
end

getvalue(o::OppositeFinCat) = o.val

@instance ThFinCat{Ob, Hom, Gen, Path{<:Ob,<:Gen}, FinSet} [model::OppositeFinCat{Ob,Hom,Gen}
                                      ] where {Ob,Hom,Gen} begin
  src(g::Gen)::Ob = tgt(getvalue(model), g)

  tgt(g::Gen)::Ob = src(getvalue(model), g)

  dom(f::Hom)::Ob = codom(getvalue(model), f)

  codom(f::Hom)::Ob = dom(getvalue(model), f)

  id(x::Ob)::Hom = id(getvalue(model), x)

  compose(f::Path{<:Ob,<:Gen})::Hom = compose(getvalue(model), reverse(f))

  decompose(f::Hom)::Path{<:Ob,<:Gen} = reverse(decompose(getvalue(model), f))

  ob_set()::FinSet = ob_set(getvalue(model))

  gen_set()::FinSet = gen_set(getvalue(model))
end

equations(C::OppositeFinCat) = map(equations(getvalue(C))) do x 
  reverse(x.first) => reverse(x.second)
end

function op(f::FinCat)
  v = getvalue(f) 
  v isa OppositeFinCat && return getvalue(v)  # optimization
  FinCat(OppositeFinCat(f))
end

end # module
