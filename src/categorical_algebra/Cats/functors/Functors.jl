export Functor, Transformation, ob_map, hom_map, do_compose, do_ob_map, 
       do_hom_map, dom_ob, codom_ob, component, op, co

using StructEquality

using GATlab
import GATlab: op

using ....Theories
using ..Categories
import ..Categories: dom, codom

# Functors
##########

""" Abstract base type for a functor between categories.

A functor has a domain and a codomain ([`dom`](@ref) and [`codom`](@ref)), which
are categories, and object and morphism maps, which can be evaluated using
[`ob_map`](@ref) and [`hom_map`](@ref). The functor object can also be called
directly when the objects and morphisms have distinct Julia types. This is
sometimes but not always the case (see [`Category`](@ref)), so when writing
generic code one should prefer the `ob_map` and `hom_map` functions.
"""
abstract type Functor{Dom<:Cat,Codom<:Cat} end

""" Evaluate functor on object.
"""
@inline ob_map(F::Functor, x) = do_ob_map(F, x)

""" Evaluate functor on morphism.
"""
@inline hom_map(F::Functor, f) = do_hom_map(F, f)

show_type_constructor(io::IO, ::Type{<:Functor}) = print(io, "Functor")


# Instances
#----------

(F::Functor{TypeCat{Ob,Hom}})(x::Ob) where {Ob,Hom} = ob_map(F, x)
(F::Functor{TypeCat{Ob,Hom}})(f::Hom) where {Ob,Hom} = hom_map(F, f)

# Natural transformations
#########################

""" Abstract base type for a natural transformation between functors.

A natural transformation ``α: F ⇒ G`` has a domain ``F`` and codomain ``G``
([`dom`](@ref) and [`codom`](@ref)), which are functors ``F,G: C → D`` having
the same domain ``C`` and codomain ``D``. The transformation consists of a
component ``αₓ: Fx → Gx`` in ``D`` for each object ``x ∈ C``, accessible using
[`component`](@ref) or indexing notation (`Base.getindex`).
"""
abstract type Transformation{C<:Cat,D<:Cat,Dom<:Functor,Codom<:Functor} end

""" Component of natural transformation.
"""
function component end

@inline Base.getindex(α::Transformation, c) = component(α, c)

""" Domain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``C``.
"""
dom_ob(α::Transformation) = dom(dom(α)) # == dom(codom(α))

""" Codomain object of natural transformation.

Given ``α: F ⇒ G: C → D``, this function returns ``D``.
"""
codom_ob(α::Transformation) = codom(dom(α)) # == codom(codom(α))

function do_ob_map end # extended by other modules
function do_hom_map end # extended by other modules
function do_compose end # extended by other modules