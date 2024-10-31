""" 2-category of categories, functors, and natural transformations.

Categories in mathematics appear in the large, often as categories of sets with
extra structure, and in the small, as algebraic structures that generalize
groups, monoids, preorders, and graphs. This division manifests in Catlab as
well. Large categories (in spirit, if not in the [technical
sense](https://ncatlab.org/nlab/show/large+category)) occur throughout Catlab as
`@instance`s of the theory of categories. For computational reasons, small
categories are usually presented by generators and relations.

This module provides a minimal interface to accomodate both situations. Category
instances are supported through the wrapper type [`TypeCat`](@ref). Finitely
presented categories are provided by another module, [`FinCats`](@ref).
"""
module Categories
export Category, TypeCat, Cat, Functor, Transformation, dom, codom, compose, id,
  ob, hom, is_hom_equal, ob_map, hom_map, dom_ob, codom_ob, component,
  OppositeCat, op, co, CatC, Cat2

using StructEquality

using GATlab
import GATlab: op, getvalue
import ....Theories: ThCategory2, ob, hom, @default_model
import .ThCategory2: dom, codom, compose, ⋅, ∘, id, composeH, *

# Categories
############

""" Abstract base type for a category. Both `Category` and `FinCat` subtype it.

The objects and morphisms in the category have Julia types `Ob` and `Hom`,
respectively. Note that these types do *not* necessarily form an `@instance` of
the theory of categories, as they may not meaningfully form a category outside
the context of this object. For example, a finite category regarded as a
reflexive graph with a composition operation might have type `Cat{Int,Int}`,
where the objects and morphisms are numerical identifiers for vertices and edges
in the graph.

The basic operations available in any category are: [`dom`](@ref),
[`codom`](@ref), [`id`](@ref), [`compose`](@ref).
"""
abstract type AbsCategory{Ob,Hom} end

const AbsCat = AbsCategory

const C{Ob,Hom} = Model{Tuple{Ob,Hom}}

abstract type CatImpl{Ob,Hom} <: C{Ob,Hom} end

"""
A (possibly) large category with ob/hom given by Julia types. A wrapper around 
some implementation of the theory of categories.

Possible additions to the interface:

ob(::Cat, x::Any)::Ob (better named: parse_ob, likewise for hom) 
"""
@struct_hash_equal struct Category{Ob,Hom} <: AbsCategory{Ob, Hom}
  mod::CatImpl{Ob, Hom}
  function Category(m::CatImpl{Ob,Hom}) where {Ob,Hom}
    implements(m, ThCategory) ? new{Ob,Hom}(m) : error("Bad model")
  end 
end 

""" Alias for [`Category`](@ref).
"""
const Cat = Category

getvalue(c::Cat) = c.mod

dom(c::AbsCat{Ob,Hom}, f::Hom) where {Ob,Hom} = dom[getvalue(c)](f)

codom(c::AbsCat{Ob,Hom}, f::Hom) where {Ob,Hom} = codom[getvalue(c)](f)

id(c::AbsCat{Ob,Hom}, x::Ob) where {Ob,Hom} = id[getvalue(c)](x)

compose(c::AbsCat{Ob,Hom}, f::Hom, g::Hom) where {Ob,Hom} = 
  compose[getvalue(c)](f,g)

compose(c::AbsCat{Ob,Hom}, fs::AbstractVector{<:Hom}) where {Ob,Hom} = 
  reduce(compose[getvalue(c)], fs)
 
Base.show(io::IO, m::AbsCat) = Base.show(io, getvalue(m))

# Implementations
#----------------

include("CatImpls/TypeCat.jl")

include("CatImpls/OpCat.jl")


# Functors
##########

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
# Note that, in order to have the same interface for Fin(Dom)Functors, we have
# Hom Generators in the theory, where normal functors are a special case 
# where Homs and Hom Generators are the same
@theory ThFunctor begin
  DomOb::TYPE; CodomOb::TYPE; DomHom::TYPE; CodomHom::TYPE;
  DomGen::TYPE; CodomGen::TYPE
  DomCat::TYPE; CodomCat::TYPE
  dom()::DomCat
  codom()::CodomCat
  ob_map(o::DomOb)::CodomOb
  hom_map(o::DomGen)::CodomHom
end

const F{DO,CO,DH,CH,DG,CG,DC<:AbsCat{DO,DH},CC<:AbsCat{CO,CH}} = 
  Model{Tuple{DO,CO,DH,CH,DG,CG,DC,CC}}

""" Abstract base type for a functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Category`](@ref)), so when writing
generic code one should prefer the `ob_map` and `hom_map` functions.
"""
abstract type AbsFunctor{DomOb,CodomOb,DomHom,CodomHom,DomGen,CodomGen,DomCat,CodomCat} end

abstract type AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC} <: F{DO,CO,DH,CH,DG,CG,DC,CC} end

""" Impl where Generators and Homs are the same """
abstract type FunctorImpl{DO,CO,DH,CH,DC,CC} <: AbsFunctorImpl{DO,CO,DH,CH,DH,CH,DC,CC} end

"""
Wrapper of an implementation of ThFunctor
"""
@struct_hash_equal struct Functor{DO,CO,DH,CH,DG,CG,DC,CC
                                 } <: AbsFunctor{DO,CO,DH,CH,DG,CG,DC,CC}
  impl::AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC}
  function Functor{DO,CO,DH,CH,DG,CG,DC,CC}(
      impl::AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC}
      ) where {DO,CO,DH,CH,DG,CG,DC,CC}
    implements(impl, ThFunctor) || error("Bad model")
    ThFunctor.dom[impl]() isa DC || error("Bad dom not a $DC")
    ThFunctor.codom[impl]() isa CC || error("Bad codom")
    new{DO,CO,DH,CH,DG,CG,DC,CC}(impl)
  end
end 

Functor(impl::AbsFunctorImpl{DO,CO,DH,CH,DG,CG,DC,CC}
  ) where {DO,CO,DH,CH,DG,CG,DC,CC} = Functor{DO,CO,DH,CH,DG,CG,DC,CC}(impl)

Functor(impl::FunctorImpl{DO,CO,DH,CH,DC,CC}) where {DO,CO,DH,CH,DC,CC} = 
  Functor{DO,CO,DH,CH,DH,CH,DC,CC}(impl)
  
getvalue(f::Functor) = f.impl

Base.show(io::IO, s::Functor) = show(io, getvalue(s))

ob_map(F::Functor{DO}, x::DO) where DO = ob_map[getvalue(F)](x)

""" Apply functor to a generating hom of the domain """
hom_map(F::Functor{<:Any, <:Any, <:Any, <:Any, DG}, x::DG) where DG = 
  hom_map[getvalue(F)](x)

dom(f::Functor) = dom[getvalue(f)]()

codom(f::Functor) = codom[getvalue(f)]()

# This method is ambiguous if DomOb == DomHom/DomGen
(F::Functor{DomOb})(x::DomOb) where DomOb = ob_map(F, x)

# This method is ambiguous if DomOb == DomHom/DomGen
(F::Functor{<:Any,<:Any,DomHom})(x::DomHom) where DomHom = hom_map(F, x)

show_type_constructor(io::IO, ::Type{<:Functor}) = print(io, "Functor")

function show_domains(io::IO, f; domain::Bool=true, codomain::Bool=true,
                      recurse::Bool=true)
  if get(io, :hide_domains, false)
    print(io, "…")
  else
    if domain
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), dom(f))
    end
    if codomain
      domain && print(io, ", ")
      show(IOContext(io, :compact=>true, :hide_domains=>!recurse), codom(f))
    end
  end
end

# Implementations
#----------------
include("FunctorImpls/IdFunctor.jl")

include("FunctorImpls/CompFunctor.jl")

include("FunctorImpls/CallFunctor.jl")

include("FunctorImpls/OpFunctor.jl")

# Category of Categories
########################

struct CatC <: Model{Tuple{AbsCategory, AbsFunctor}} end

@instance ThCategory{AbsCategory, AbsFunctor} [model::CatC] begin
  dom(f::AbsFunctor)::AbsCategory = dom(f)

  codom(f::AbsFunctor)::AbsCategory = codom(f)

  id(c::AbsCategory) = Functor(c)

  compose(f::AbsFunctor, g::AbsFunctor) = Functor(CompositeFunctor(f,g))
end 

@default_model ThCategory{AbsCategory, AbsFunctor} [model::CatC]


# Natural transformations
#########################

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
@theory ThTransformation begin
  DomOb::TYPE; CodomOb::TYPE; domHom::TYPE; codomHom::TYPE; 
  Fun::TYPE;
  dom()::Fun 
  codom()::Fun
  component(x::DomOb)::codomHom
end

const N{DO,CO,DH,CH} = Model{Tuple{DO,CO,DH,CH,
                                   Functor{DO,CO,DH,CH},Functor{DO,CO,DH,CH}}}

abstract type NatTransImpl{DO,CO,DH,CH} <: N{DO,CO,DH,CH} end

""" Abstract base type for a natural transformation between functors.

A natural transformation ``α: F ⇒ G`` has a domain ``F`` and codomain ``G``
([`dom`](@ref) and [`codom`](@ref)), which are functors ``F,G: C → D`` having
the same domain ``C`` and codomain ``D``. The transformation consists of a
component ``αₓ: Fx → Gx`` in ``D`` for each object ``x ∈ C``, accessible using
[`component`](@ref) or indexing notation (`Base.getindex`).
"""
@struct_hash_equal struct Transformation{DO,CO,DH,CH} 
  impl::NatTransImpl{DO,CO,DH,CH}
  function Transformation(i::NatTransImpl{DO,CO,DH,CH}) where {DO,CO,DH,CH}
    implements(i, ThTransformation) || error("Bad model")
    # check domains and codomains of functors are equal?
    new{DO,CO,DH,CH}(i)
  end
end

getvalue(t::Transformation) = t.impl 

""" Component of natural transformation.
"""
component(t::Transformation{DO}, x::DO) where DO = 
  ThTransformation.component[getvalue(t)](x)

@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

# Implementations
#----------------

include("NatTransImpls/IdTrans.jl")
  

# # 2-category of categories
# ##########################

struct Cat2 <: Model{Tuple{Cat,Functor,Transformation}} end 

@instance ThCategory2{Cat,Functor,Transformation} [model::Cat2] begin
  dom(F::Functor) = ThFunctor.dom[getvalue(F)]()
  codom(F::Functor) = ThFunctor.codom[getvalue(F)]()
  id(C::Cat) = Transformation(C)

  function compose(F::Functor, G::Functor)
    compose_id(F, G)
  end

  dom(α::Transformation) = ThTransformation.dom[getvalue(α)]()
  codom(α::Transformation) = ThTransformation.codom[getvalue(α)]()
  id(F::Functor) = Transformation(F)

  function compose(α::Transformation, β::Transformation)
    compose_id(α, β)
  end
  function composeH(α::Transformation, β::Transformation)
    composeH_id(α, β)
  end
  function composeH(α::Transformation, H::Functor)
    composeH_id(α, H)
  end
  function composeH(F::Functor, β::Transformation)
    composeH_id(F, β)
  end
end


# TODO: port over the rest of 2 category code
# # XXX: Is this normalization of identities using multiple dispatch a good idea?
# # Unlike in `Sets`, it doesn't feel great since it requires so much boilerplate.

# @inline compose_id(F::Functor, G::Functor) = do_compose(F, G)
# @inline compose_id(F::Functor, ::IdentityFunctor) = F
# @inline compose_id(::IdentityFunctor, G::Functor) = G
# @inline compose_id(F::IdentityFunctor, ::IdentityFunctor) = F

# @inline compose_id(α::Transformation, β::Transformation) = do_compose(α, β)
# @inline compose_id(α::Transformation, ::IdentityTransformation) = α
# @inline compose_id(::IdentityTransformation, β::Transformation) = β
# @inline compose_id(α::IdentityTransformation, ::IdentityTransformation) = α

# @inline composeH_id(α::Transformation, β::Transformation) = do_composeH(α, β)
# @inline composeH_id(α::Transformation, ::IdIdTransformation) = α
# @inline composeH_id(::IdIdTransformation, β::Transformation) = β
# @inline composeH_id(α::IdIdTransformation, ::IdIdTransformation) = α

# @inline composeH_id(α::Transformation, H::Functor) = do_composeH(α, H)
# @inline composeH_id(α::Transformation, ::IdentityFunctor) = α
# @inline composeH_id(α::IdentityTransformation, H::Functor) =
#   id(compose_id(dom(α), H))
# @inline composeH_id(α::IdentityTransformation, ::IdentityFunctor) = α

# @inline composeH_id(F::Functor, β::Transformation) = do_composeH(F, β)
# @inline composeH_id(::IdentityFunctor, β::Transformation) = β
# @inline composeH_id(F::Functor, β::IdentityTransformation) =
#   id(compose_id(F, dom(β)))
# @inline composeH_id(::IdentityFunctor, β::IdentityTransformation) = β

# do_compose(F::Functor, G::Functor) = CompositeFunctor(F, G)

# @inline function do_composeH(α::Transformation, β::Transformation)
#   do_composeH(α, β, Val{:covariant})
# end
# function do_composeH(α::Transformation, β::Transformation,
#                      ::Type{Val{:covariant}})
#   G, H = codom(α), dom(β)
#   compose_id(composeH_id(α, H), composeH_id(G, β))
# end
# function do_composeH(α::Transformation, β::Transformation,
#                      ::Type{Val{:contravariant}})
#   F, K = dom(α), codom(β)
#   compose_id(composeH_id(F, β), composeH_id(α, K))
# end


# """ Oppositization 2-functor.

# The oppositization endo-2-functor on Cat, sending a category to its opposite, is
# covariant on objects and morphisms and contravariant on 2-morphisms, i.e., is a
# 2-functor ``op: Catᶜᵒ → Cat``. For more explanation, see the
# [nLab](https://ncatlab.org/nlab/show/opposite+category).
# """
# op(C::Cat) = OppositeCat(C)
# op(F::Functor) = OppositeFunctor(F)
# #op(α::Transformation) = OppositeTransformation(α)
# op(C::OppositeCat) = C.cat
# op(F::OppositeFunctor) = F.func
# #op(α::OppositeTransformation) = α.trans

""" 2-cell dual of a 2-category.
"""
function co end

end
