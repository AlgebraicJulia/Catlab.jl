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
export Category, Cat, Functor, Transformation, dom, codom, compose, id,
  ob, hom, is_hom_equal, ob_map, hom_map, dom_ob, codom_ob, component,
  OppositeCat, op, co, CatC, getmodel

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

const C{Ob,Hom} = Model{Tuple{Ob,Hom}}

"""
A (possibly) large category with ob/hom given by Julia types. A wrapper around 
some implementation of the theory of categories.

Possible additions to the interface:

ob(::Cat, x::Any)::Ob (better named: parse_ob, likewise for hom) 
"""
struct Category{Ob,Hom} <: AbsCategory{Ob, Hom}
  mod::C{Ob, Hom}
  function Category(m::C{Ob,Hom}) where {Ob,Hom}
    implements(m, ThCategory) ? new{Ob,Hom}(m) : error("Bad model")
  end 
end 

""" Alias for [`Category`](@ref).
"""
const Cat = Category

getvalue(c::Cat) = c.mod
getmodel(c::Cat) = c.mod

Base.show(io::IO, m::Cat) = Base.show(io, getvalue(m))

# Functors
##########

# The equations that come with this will be less tedious to do when colimits 
# of GATs are a thing
@theory ThFunctor begin
  DomOb::TYPE
  CodomOb::TYPE
  DomHom::TYPE
  CodomHom::TYPE
  DomCat::TYPE 
  CodomCat::TYPE
  Functor′::TYPE
  dom(f::Functor′)::DomCat
  codom(f::Functor′)::CodomCat
  ob_map(f::Functor′, o::DomOb)::CodomOb
  hom_map(f::Functor′, o::DomHom)::CodomHom
end

const F{DO,CO,DH,CH,I} = Model{Tuple{DO,CO,DH,CH,Cat{DO,DH},Cat{CO,CH},I}}

""" Abstract base type for a functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Category`](@ref)), so when writing
generic code one should prefer the `ob_map` and `hom_map` functions.
"""
abstract type AbsFunctor{DomOb,CodomOb,DomHom,CodomHom} end
abstract type FunctorImpl{DomOb,CodomOb,DomHom,CodomHom} end 
"""
Informally (though could be made explicit via a GAT) we have some implementation
for which 
"""
struct Functor{DomOb,CodomOb,DomHom,CodomHom} <: AbsFunctor{DomOb,CodomOb,DomHom,CodomHom}
  impl::FunctorImpl{DomOb,CodomOb,DomHom,CodomHom}
  m::Any
  function Functor(impl::T, m::F{DO,CO,DH,CH,T}) where {DO,CO,DH,CH, T<:FunctorImpl{DO,CO,DH,CH}}
    implements(m, ThFunctor) || error("Bad model")
    new{DO,CO,DH,CH}(impl, m)
  end
end 

getvalue(f::Functor) = f.impl

getmodel(f::Functor) = f.m

Base.show(io::IO, s::Functor) = show(io, getvalue(s))

ob_map(F::Functor, x) = ob_map[getmodel(F)](getvalue(F), x)

hom_map(F::Functor, x) = hom_map[getmodel(F)](getvalue(F), x)

dom(f::Functor) = dom[getmodel(f)](getvalue(f))

codom(f::Functor) = codom[getmodel(f)](getvalue(f))

# This method is ambiguous if DomOb == DomHom
(F::Functor{DomOb,<:Any,<:Any,<:Any})(x::DomOb) where DomOb = ob_map(F, x)

# This method is ambiguous if DomOb == DomHom
(F::Functor{<:Any,<:Any,DomHom,<:Any})(x::DomHom) where DomHom = hom_map(F, x)


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

""" Identity functor on a category.
"""
@struct_hash_equal struct IdentityFunctor{Ob,Hom} <: FunctorImpl{Ob,Ob,Hom,Hom}
  dom::Cat{Ob,Hom}
end

function Base.show(io::IO, F::IdentityFunctor)
  print(io, "id(")
  #show_domains(io, F, codomain=false)
  print(io, ")")
end

@struct_hash_equal struct IdFunctorImpl{O,H} <: F{O,O,H,H, IdentityFunctor{O,H}}
end 

@instance ThFunctor{O,O,H,H,Cat{O,H},Cat{O,H}, IdentityFunctor{O,H}
                   } [model::IdFunctorImpl{O,H}] where {O,H} begin 
  dom(i::IdentityFunctor{O,H}) = i.dom

  codom(i::IdentityFunctor{O,H}) = i.dom

  ob_map(::IdentityFunctor{O,H}, x::O) = x

  hom_map(::IdentityFunctor{O,H}, x::H) = x
end

Functor(i::IdentityFunctor{O,H}) where {O,H} = Functor(i, IdFunctorImpl{O,H}())

""" Composite of functors.
"""
@struct_hash_equal struct CompositeFunctor{AO,BO,CO,AH,BH,CH} <: FunctorImpl{AO,CO,AH,BH}
  fst::Functor{AO,BO,AH,BH}
  snd::Functor{BO,CO,BH,CH}
end
Base.first(F::CompositeFunctor) = F.fst
Base.last(F::CompositeFunctor) = F.snd

@struct_hash_equal struct CompFunctorImpl{DO,CO,DH,CH}  <: F{
  DO,CO,DH,CH,CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}}
end 

@instance ThFunctor{DO,CO,DH,CH,Cat{DO,DH},Cat{CO,CH}, 
                    CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}
                   } [model::CompFunctorImpl{DO,CO,DH,CH}
                     ] where {DO,CO,DH,CH} begin 
  dom(F::CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}) = dom(first(F))

  codom(F::CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}) = codom(last(F))

  ob_map(F::CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}, x::DO) = 
    ob_map(F.snd, ob_map(F.fst, x))

  hom_map(F::CompositeFunctor{DO,<:Any,CO,DH,<:Any,CH}, f::DH) = 
    hom_map(F.snd, hom_map(F.fst, f))
end

function Base.show(io::IO, F::CompositeFunctor)
  print(io, "compose(")
  show(io, first(F))
  print(io, ", ")
  show(io, last(F))
  print(io, ")")
end

Functor(i::CompositeFunctor{DO,CO,DH,CH}) where {DO,CO,DH,CH} = 
  Functor(i, CompFunctorImpl{DO,CO,DH,CH}())


# Callables
#----------

""" Functor defined by two Julia callables, an object map and a morphism map.
"""
@struct_hash_equal struct FunctorCallable{
    DomOb,CodomOb,DomHom,CodomHom} <: FunctorImpl{DomOb,CodomOb,DomHom,CodomHom}
  ob_map::Any
  hom_map::Any
  dom::Cat{DomOb,DomHom}
  codom::Cat{CodomOb,CodomHom}
end

@struct_hash_equal struct FunctorCallableImpl{DO,CO,DH,CH} <: F{
  DO,CO,DH,CH,FunctorCallable{DO,CO,DH,CH}}
end 

@instance ThFunctor{DO,CO,DH,CH,Cat{DO,DH},Cat{CO,CH}, FunctorCallable{DO,CO,DH,CH}
                   } [model::FunctorCallableImpl{DO,CO,DH,CH}] where {DO,CO,DH,CH} begin 
  dom(F::FunctorCallable{DO,CO,DH,CH}) = F.dom

  codom(F::FunctorCallable{DO,CO,DH,CH}) = F.codom

  ob_map(F::FunctorCallable{DO,CO,DH,CH}, x::DO) = F.ob_map(x) 

  hom_map(F::FunctorCallable{DO,CO,DH,CH}, f::DH) = F.hom_map(f)
end

Functor(f::Function, g::Function, C::Cat{DO,DH}, D::Cat{CO,CH}) where {DO,CO,DH,CH} = 
  Functor(FunctorCallable(f, g, C, D), FunctorCallableImpl{DO,CO,DH,CH}())

# Category of Categories
########################

struct CatC <: Model{Tuple{AbsCategory, AbsFunctor}} end

@instance ThCategory{AbsCategory, AbsFunctor} [model::CatC] begin
  dom(f::AbsFunctor)::AbsCategory = dom(f)

  codom(f::AbsFunctor)::AbsCategory = codom(f)

  id(c::AbsCategory) = Functor(IdentityFunctor(c))

  compose(f::AbsFunctor, g::AbsFunctor) = Functor(CompositeFunctor(f,g))
end 

@default_model ThCategory{AbsCategory, AbsFunctor} [model::CatC]

# if false 

# # Natural transformations
# #########################

# """ Abstract base type for a natural transformation between functors.

# A natural transformation ``α: F ⇒ G`` has a domain ``F`` and codomain ``G``
# ([`dom`](@ref) and [`codom`](@ref)), which are functors ``F,G: C → D`` having
# the same domain ``C`` and codomain ``D``. The transformation consists of a
# component ``αₓ: Fx → Gx`` in ``D`` for each object ``x ∈ C``, accessible using
# [`component`](@ref) or indexing notation (`Base.getindex`).
# """
# abstract type Transformation{C<:Cat,D<:Cat,Dom<:Functor,Codom<:Functor} end

# """ Component of natural transformation.
# """
# function component end

# @inline Base.getindex(α::Transformation, c) = component(α, c)

# """ Domain object of natural transformation.

# Given ``α: F ⇒ G: C → D``, this function returns ``C``.
# """
# dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

# """ Codomain object of natural transformation.

# Given ``α: F ⇒ G: C → D``, this function returns ``D``.
# """
# codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

# @struct_hash_equal struct IdentityTransformation{C<:Cat,D<:Cat,Dom<:Functor{C,D}} <:
#      Transformation{C,D,Dom,Dom}
#   dom::Dom
# end

# codom(α::IdentityTransformation) = α.dom

# function component(α::IdentityTransformation, x)
#   F = dom(α)
#   id(codom(F), ob_map(F, x))
# end

# const IdIdTransformation{C<:Cat} = IdentityTransformation{C,C,IdentityFunctor{C}}

# # 2-category of categories
# ##########################

# @instance ThCategory2{Cat,Functor,Transformation} begin
#   dom(F::Functor) = F.dom
#   codom(F::Functor) = F.codom
#   id(C::Cat) = IdentityFunctor(C)

#   function compose(F::Functor, G::Functor)
#     compose_id(F, G)
#   end

#   dom(α::Transformation) = α.dom
#   codom(α::Transformation) = α.codom
#   id(F::Functor) = IdentityTransformation(F)

#   function compose(α::Transformation, β::Transformation)
#     compose_id(α, β)
#   end
#   function composeH(α::Transformation, β::Transformation)
#     composeH_id(α, β)
#   end
#   function composeH(α::Transformation, H::Functor)
#     composeH_id(α, H)
#   end
#   function composeH(F::Functor, β::Transformation)
#     composeH_id(F, β)
#   end
# end

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

# # Oppositization 2-functor
# #-------------------------

# """ Opposite category, where morphism are reversed.

# Call `op(::Cat)` instead of directly instantiating this type.
# """
# @struct_hash_equal struct OppositeCat{Ob,Hom,Size<:CatSize,C<:Cat{Ob,Hom,Size}} <:
#     Cat{Ob,Hom,Size}
#   cat::C
# end

# ob(C::OppositeCat, x) = ob(C.cat, x)
# hom(C::OppositeCat, f) = hom(C.cat, f)

# dom(C::OppositeCat, f) = codom(C.cat, f)
# codom(C::OppositeCat, f) = dom(C.cat, f)
# id(C::OppositeCat, x) = id(C.cat, x)
# compose(C::OppositeCat, f, g) = compose(C.cat, g, f)

# """ Opposite functor, given by the same mapping between opposite categories.

# Call `op(::Functor)` instead of directly instantiating this type.
# """
# @struct_hash_equal struct OppositeFunctor{C,D,F<:Functor{C,D}} <: Functor{C,D}
#     # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
#     #Functor{OppositeCat{C},OppositeCat{D}}
#   func::F
# end

# dom(F::OppositeFunctor) = op(dom(F.func))
# codom(F::OppositeFunctor) = op(codom(F.func))

# do_ob_map(F::OppositeFunctor, x) = ob_map(F.func, x)
# do_hom_map(F::OppositeFunctor, f) = hom_map(F.func, f)

# do_compose(F::OppositeFunctor, G::OppositeFunctor) =
#   OppositeFunctor(do_compose(F.func, G.func))

# #= Not yet needed because the only natural transformations we currently support
# #are `FinTransformationMap`, for which can just implement `op` directly.

# """ Opposite natural transformation between opposite functors.

# Call `op(::Transformation)` instead of directly instantiating this type.
# """
# @struct_hash_equal struct OppositeTransformation{C,D,F,G,T<:Transformation{C,D,F,G}} <: Transformation{C,D,F,G}
#     # XXX: Requires more type parameters: ObC, HomC, ObD, HomD.
#     #Transformation{OppositeCat{C},OppositeCat{D},OppositeFunctor{C,D,G},OppositeFunctor{C,D,F}}
#   trans::T
# end

# dom(α::OppositeTransformation) = op(codom(α.trans))
# codom(α::OppositeTransformation) = op(dom(α.trans))

# component(α::OppositeTransformation, x) = component(α.trans, x)

# do_compose(α::OppositeTransformation, β::OppositeTransformation) =
#   OppositeTransformation(do_compose(β.trans, α.trans))
# do_composeH(α::OppositeTransformation, β::OppositeTransformation) =
#   OppositeTransformation(do_composeH(α.trans, β.trans))
# do_composeH(F::OppositeFunctor, β::OppositeTransformation) =
#   OppositeTransformation(do_composeH(F.func, β.trans))
# do_composeH(α::OppositeTransformation, H::OppositeFunctor) =
#   OppositeTransformation(do_composeH(α.trans, H.func))
# =#

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

# """ 2-cell dual of a 2-category.
# """
# function co end
# end 

end
