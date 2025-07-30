module OpFinCat 
export OppositeFinCat

using StructEquality

using ..FinCats 
import ..FinCats: ob_generators, hom_generators, ob_generator, hom_generator


const OppositeFinCat{Ob,Hom} = OppositeCat{Ob,Hom,FinCatSize}

ob_generators(C::OppositeFinCat) = ob_generators(C.cat)
hom_generators(C::OppositeFinCat) = hom_generators(C.cat)

ob_generator(C::OppositeCat, x) = ob_generator(C.cat, x)
hom_generator(C::OppositeCat, f) = hom_generator(C.cat, f)

end # module
