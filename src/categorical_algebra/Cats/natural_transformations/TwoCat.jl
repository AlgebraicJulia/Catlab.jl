module TwoCat 
export Cat2, co

using StructEquality 
using GATlab 

using .....Theories: ThCategory2
using ...Cats, ..Transformations

using .ThCategory2

# 2-category of categories
##########################

@struct_hash_equal struct Cat2 end 

@instance ThCategory2{AbsCat,AbsFunctor,Transformation} [model::Cat2] begin
  
  dom(F::AbsFunctor) = ThFunctor.dom[getvalue(F)]()
  
  codom(F::AbsFunctor) = ThFunctor.codom[getvalue(F)]()
  
  id(C::AbsCat) = (C isa FinCat ? FinFunctor : Functor)(C)

  compose(F::AbsFunctor, G::AbsFunctor) = compose_abs_functor(F, G)

  dom(α::Transformation) = dom(α)

  codom(α::Transformation) = codom(α)

  id(F::AbsFunctor) = Transformation(F)

  function compose(α::Transformation, β::Transformation)
    compose_transformation(α, β)
  end

  function composeH(α::Transformation, β::Transformation)
    G, H = codom(α), dom(β)
    compose[model](composeH[model](α, H), composeH[model](G, β))
  end
  function composeH(α::Transformation, H::AbsFunctor)
    F, G = dom(α), codom(α)
    Transformation(mapvals(f->hom_map(H,f), components(α)),
                         compose[model](F, H), compose[model](G, H))
  end

  function composeH(F::AbsFunctor, β::Transformation)
    # composeH_id(F, β)
    G, H = dom(β), codom(β)
    Transformation(mapvals(c -> component(β, c), ob_map(F)),
                   compose[model](F, G), compose[model](F, H))
  end
end

function compose_transformation(α::FinTransformation, β::Transformation)
  F = dom(α)
  D = codom(F)
  Transformation(mapvals(components(α), keys=true) do c, f
                         compose(D, f, component(β, c))
                       end, F, codom(β)) #|> Transformation
end

function compose_transformation(α::Transformation, β::Transformation)
  F = dom(α)
  D = codom(F)
  Transformation(c -> compose(D, f, component.([α,β], Ref(c))...), F, codom(β))
end


end # module
