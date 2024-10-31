
# Opposite FinCats
##################

@struct_hash_equal struct OppositeFinCat{Ob,Hom,Gen} <: FinCatImpl{Ob,Hom,Gen}
  val::FinCat{Ob,Hom,Gen}
end

getvalue(o::OppositeFinCat) = o.val

@instance ThFinCat{Ob, Hom, Gen, Any} [model::OppositeFinCat{Ob,Hom,Gen}
                                      ] where {Ob,Hom,Gen} begin
  dom(f::Hom)::Ob = codom(getvalue(model), f)

  codom(f::Hom)::Ob = dom(getvalue(model), f)

  id(x::Ob)::Hom = id(getvalue(model), x)

  compose(f::Hom, g::Hom)::Hom = compose(getvalue(model), g, f)

  singleton(f::Gen)::Hom = singleton(getvalue(model), f)

  ob_generators() = ob_generators(getvalue(model))

  hom_generators() = hom_generators(getvalue(model))
end

equations(C::OppositeFinCat) = 
  map(x->reverse(x.first)=>reverse(x.second),equations(getvalue(C)))

decompose(C::OppositeFinCat{<:Any,H}, f::H) where H = 
  reverse(decompose(getvalue(C), f))

function op(f::FinCat)
  v = getvalue(f) 
  v isa OppositeFinCat && return getvalue(v)  # optimization
  FinCat(OppositeFinCat(f))
end