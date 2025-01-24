export Category, Cat, CatSize, LargeCatSize, dom, codom, compose, id, ob, hom, is_hom_equal

using StructEquality

using GATlab
import ....Theories: ThCategory, ob, hom
import .ThCategory: dom, codom, compose, ⋅, id
import ....BasicSets.SetFunctions: show_domains, show_type_constructor

# Categories
############

""" Size of a category, used for dispatch and subtyping purposes.

A [`Category`](@ref) type having a particular `CatSize` means that categories of
that type are *at most* that large.
"""
abstract type CatSize end

""" Size of a large category, such as Set.

To the extent that they form a category, we regard Julia types and functions
([`TypeCat`](@ref)) as forming a large category.
"""
struct LargeCatSize <: CatSize end

""" Abstract base type for a category.

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
abstract type Category{Ob,Hom,Size<:CatSize} end

""" Alias for [`Category`](@ref).
"""
const Cat = Category

""" Coerce or look up object in category.

Converts the input to an object in the category, which should be of type `Ob` in
a category of type `Cat{Ob,Hom}`. How this works depends on the category, but a
common case is to look up objects, which might be integers or GAT expressions,
by their human-readable name, usually a symbol.

See also: [`hom`](@ref).
"""
function ob end

""" Coerce or look up morphism in category.

See also: [`ob`](@ref).
"""
function hom end

""" Domain of morphism in category.
"""
dom(C::Cat, f) = dom(f)

""" Codomain of morphism in category.
"""
codom(C::Cat, f) = codom(f)

""" Identity morphism on object in category.
"""
id(C::Cat, x) = id(x)

""" Compose morphisms in a category.
"""
compose(C::Cat, fs...) = compose(fs...)

""" Are two morphisms in a category equal?

By default, just checks for equality of Julia objects using ``==``. In some
categories, checking equality of morphisms may involve nontrivial reasoning.
"""
is_hom_equal(C::Cat, f, g) = is_hom_equal(f, g)
is_hom_equal(f, g) = f == g
