""" 2-category of finitely presented categories.

This module is for the 2-category **Cat** what the module [`FinSets](@ref) is
for the category **Set**: a finitary, combinatorial setting where explicit
calculations can be carried out. We emphasize that the prefix `Fin` means
"finitely presented," not "finite," as finite categories are too restrictive a
notion for many purposes. For example, the free category on a graph is finite if
and only if the graph is DAG, which is a fairly special condition. This usage of
`Fin` is also consistent with `FinSet` because for sets, being finite and being
finitely presented are equivalent.
"""
module FinCats
export FinCat, Path, ob_generators, hom_generators, equations, is_discrete,
  is_free, graph, edges, src, tgt, presentation,
  FinFunctor, FinDomFunctor, is_functorial, collect_ob, collect_hom,
  FinTransformation, components, is_natural

using AutoHashEquals
using Reexport
using StaticArrays: SVector

@reexport using ..Categories
using ...GAT, ...Present, ...Syntax
import ...Present: equations
using ...Theories: Category, ObExpr, HomExpr
import ...Theories: dom, codom, id, compose, ⋅, ∘
using ...CSetDataStructures, ...Graphs, ..FreeDiagrams, ..FinSets
import ...Graphs: edges, src, tgt
import ..FreeDiagrams: FreeDiagram, diagram_type, cone_objects, cocone_objects
import ..Limits: limit, colimit
import ..Categories: Ob, ob, hom, ob_map, hom_map, component

# Categories
############

""" Abstract type for finitely presented category.
"""
abstract type FinCat{Ob,Hom} <: Cat{Ob,Hom} end

FinCat(g::HasGraph, args...; kw...) = FinCatGraph(g, args...; kw...)
FinCat(pres::Presentation, args...; kw...) =
  FinCatPresentation(pres, args...; kw...)

""" Object generators of finitely presented category.

The object generators are almost always the same as the objects. In principle,
however, it is possible to have equations between objects, so that there are
fewer objects than object generators.
"""
function ob_generators end

""" Morphism generators of finitely presented category.
"""
function hom_generators end

""" Is the category discrete?

A category is *discrete* if it is has no non-identity morphisms.
"""
is_discrete(C::FinCat) = isempty(hom_generators(C))

""" Is the category freely generated?
"""
is_free(C::FinCat) = isempty(equations(C))

Ob(C::FinCat{Int}) = FinSet(length(ob_generators(C)))

# Discrete categories
#####################

""" Discrete category on a finite set.

The only morphisms in a discrete category are the identities, which in this
implementation are identified with the objects.
"""
@auto_hash_equals struct DiscreteCat{Ob,S<:FinSet{<:Any,Ob}} <: FinCat{Ob,Ob}
  set::S
end
DiscreteCat(n::Integer) = DiscreteCat(FinSet(n))

FinCat(s::Union{FinSet,Integer}) = DiscreteCat(s)

ob_generators(C::DiscreteCat) = C.set
hom_generators(::DiscreteCat) = ()
is_discrete(::DiscreteCat) = true

dom(C::DiscreteCat{T}, f) where T = f::T
codom(C::DiscreteCat{T}, f) where T = f::T
id(C::DiscreteCat{T}, x) where T = x::T
compose(C::DiscreteCat{T}, f, g) where T = (f::T == g::T) ? f :
  error("Nontrivial composite in discrete category: $f != $g")

# Categories on graphs
######################

""" Abstract type for category backed by finite generating graph.
"""
abstract type FinCatGraph{Ob,Hom} <: FinCat{Ob,Hom} end

""" Generating graph for a finitely presented category.
"""
graph(C::FinCatGraph) = C.graph

ob_generators(C::FinCatGraph) = vertices(graph(C))
hom_generators(C::FinCatGraph) = edges(graph(C))

# Paths in graphs
#----------------

""" Path in a graph.

The path is allowed to be empty but always has definite start and end points
(source and target vertices).
"""
@auto_hash_equals struct Path{V,E,Edges<:AbstractVector{E}}
  edges::Edges
  src::V
  tgt::V
end
edges(path::Path) = path.edges
src(path::Path) = path.src
tgt(path::Path) = path.tgt

function Path(g::HasGraph, es::AbstractVector)
  !isempty(es) || error("Nonempty edge list needed for nontrivial path")
  all(e -> has_edge(g, e), es) || error("Path has edges not contained in graph")
  Path(es, src(g, first(es)), tgt(g, last(es)))
end

function Path(g::HasGraph, e)
  has_edge(g, e) || error("Edge $e not contained in graph $g")
  Path(SVector(e), src(g,e), tgt(g,e))
end

function Base.empty(::Type{Path}, g::HasGraph, v::T) where T
  has_vertex(g, v) || error("Vertex $v not contained in graph $g")
  Path(SVector{0,T}(), v, v)
end

function Base.vcat(p1::Path, p2::Path)
  tgt(p1) == src(p2) ||
    error("Path start/end points do not match: $(tgt(p1)) != $(src(p2))")
  Path(vcat(edges(p1), edges(p2)), src(p1), tgt(p2))
end

""" Abstract type for category whose morphisms are paths in a graph.

(Or equivalence classes of paths in a graph, but we compute with
"""
const FinCatPathGraph{V,E} = FinCatGraph{V,Path{V,E}}

dom(C::FinCatPathGraph, e) = src(graph(C), e)
dom(C::FinCatPathGraph, path::Path) = src(path)
codom(C::FinCatPathGraph, e) = tgt(graph(C), e)
codom(C::FinCatPathGraph, path::Path) = tgt(path)

id(C::FinCatPathGraph, x) = empty(Path, graph(C), x)
compose(C::FinCatPathGraph, fs...) =
  reduce(vcat, coerce_path(graph(C), f) for f in fs)

ob(C::FinCatPathGraph, x) = has_vertex(graph(C), x) ? x :
  error("Vertex $x not contained in graph $(graph(C))")
hom(C::FinCatPathGraph, f) = coerce_path(graph(C), f)

coerce_path(g::HasGraph, path::Path) = path
coerce_path(g::HasGraph, x) = Path(g, x)

# Free category on graph
#-----------------------

""" Free category generated by a finite graph.

The objects of the free category are vertices in the graph and the morphisms are
(possibly empty) paths.
"""
@auto_hash_equals struct FreeCatGraph{G<:HasGraph} <: FinCatPathGraph{Int,Int}
  graph::G
end

FinCatGraph(g::HasGraph) = FreeCatGraph(g)

is_free(::FreeCatGraph) = true

# Category on graph with equations
#---------------------------------

""" Category presented by a finite graph together with path equations.

The objects of the category are vertices in the graph and the morphisms are
paths, quotiented by the congruence relation generated by the path equations.
See (Spivak, 2014, *Category theory for the sciences*, §4.5).
"""
@auto_hash_equals struct FinCatGraphEq{G<:HasGraph,Eqs<:AbstractVector{<:Pair}} <:
    FinCatPathGraph{Int,Int}
  graph::G
  equations::Eqs
end

equations(C::FinCatGraphEq) = C.equations

function FinCatGraph(g::HasGraph, eqs::AbstractVector)
  eqs = map(eqs) do eq
    lhs, rhs = coerce_path(g, first(eq)), coerce_path(g, last(eq))
    (src(lhs) == src(rhs) && tgt(lhs) == tgt(rhs)) ||
      error("Paths $lhs and $rhs in equation do not have equal (co)domains")
    lhs => rhs
  end
  FinCatGraphEq(g, eqs)
end

# Symbolic categories
#####################

""" Category defined by a `Presentation` object.
"""
struct FinCatPresentation{Ob,Hom} <: FinCat{Ob,Hom}
  presentation::Presentation

  function FinCatPresentation(pres::Presentation)
    new{pres.syntax.Ob,pres.syntax.Hom}(pres)
  end
end

presentation(C::FinCatPresentation) = C.presentation
ob_generators(C::FinCatPresentation) = generators(presentation(C), :Ob)
hom_generators(C::FinCatPresentation) = generators(presentation(C), :Hom)
equations(C::FinCatPresentation) = equations(presentation(C))

ob(C::FinCatPresentation, x) = ob(C, presentation(C)[x])
ob(C::FinCatPresentation, x::GATExpr) = x
  # FIXME: Commented for now because `DataMigration` uses for attr types.
  # gat_typeof(x) == :Ob ? x : error("Expression $x is not an object")

hom(C::FinCatPresentation, f) = hom(C, presentation(C)[f])
hom(C::FinCatPresentation, f::GATExpr) = f
  # FIXME: Commented for now because `DataMigration` uses for attributes.
  # gat_typeof(f) == :Hom ? f : error("Expression $f is not a morphism")
hom(C::FinCatPresentation, fs::AbstractVector) =
  mapreduce(f -> hom(C, f), compose, fs)

# Functors
##########

""" A functor out of a finitely presented category.
"""
const FinDomFunctor{Dom<:FinCat,Codom<:Cat} = Functor{Dom,Codom}

FinDomFunctor(maps::NamedTuple{(:V,:E)}, dom::FinCatGraph, codom::Cat) =
  FinDomFunctor(maps.V, maps.E, dom, codom)
FinDomFunctor(ob_map, dom::DiscreteCat, codom::Cat{Ob,Hom}) where {Ob,Hom} =
  FinDomFunctor(ob_map, empty(ob_map, Hom), dom, codom)
FinDomFunctor(ob_map, ::Nothing, dom::DiscreteCat, codom::Cat) =
  FinDomFunctor(ob_map, dom, codom)

# Diagram interface. See `FreeDiagrams` module.
diagram_type(F::FinDomFunctor{Dom,Codom}) where {Ob,Hom,Dom,Codom<:Cat{Ob,Hom}} =
  Tuple{Ob,Hom}
cone_objects(F::FinDomFunctor) = collect_ob(F)
cocone_objects(F::FinDomFunctor) = collect_ob(F)

function hom_map(F::FinDomFunctor{<:FinCatPathGraph}, path::Path)
  D = codom(F)
  mapreduce(e -> hom_map(F, e), (gs...) -> compose(D, gs...),
            edges(path), init=id(D, ob_map(F, src(path))))
end

ob_map(F::FinDomFunctor, x::GATExpr{:generator}) = ob_map(F, first(x))
hom_map(F::FinDomFunctor, f::GATExpr{:generator}) = hom_map(F, first(f))
hom_map(F::FinDomFunctor, f::GATExpr{:id}) = id(codom(F), ob_map(F, dom(f)))

function hom_map(F::FinDomFunctor, f::GATExpr{:compose})
  D = codom(F)
  mapreduce(f -> hom_map(F, f), (gs...) -> compose(D, gs...), args(f))
end

(F::FinDomFunctor)(expr::ObExpr) = ob_map(F, expr)
(F::FinDomFunctor)(expr::HomExpr) = hom_map(F, expr)

""" Is the purported functor on a presented category functorial?

This function checks that functor preserves domains and codomains. When
`check_equations` is `true` (the default), it also checks that the functor
preserves all equations in the domain category. Note that in some cases this may
not be possible.

See also: [`is_natural`](@ref).
"""
function is_functorial(F::FinDomFunctor; check_equations::Bool=false)
  C, D = dom(F), codom(F)
  all(hom_generators(C)) do f
    g = hom_map(F, f)
    dom(D,g) == ob_map(F, dom(C,f)) && codom(D,g) == ob_map(F, codom(C,f))
  end || return false

  if check_equations
    all(equations(C)) do (lhs, rhs)
      is_hom_equal(D, hom_map(F, lhs), hom_map(F, rhs))
    end || return false
  end

  true
end

""" A functor between finitely presented categories.
"""
const FinFunctor{Dom<:FinCat,Codom<:FinCat} = FinDomFunctor{Dom,Codom}

FinFunctor(maps, dom::FinCat, codom::FinCat) = FinDomFunctor(maps, dom, codom)
FinFunctor(ob_map, hom_map, dom::FinCat, codom::FinCat) =
  FinDomFunctor(ob_map, hom_map, dom, codom)
FinFunctor(ob_map, hom_map, dom::Presentation, codom::Presentation) =
  FinDomFunctor(ob_map, hom_map, FinCat(dom), FinCat(codom))

# Mapping-based functors
#-----------------------

""" Functor out of a finitely presented category given by explicit mappings.
"""
@auto_hash_equals struct FinDomFunctorMap{Dom<:FinCat, Codom<:Cat,
    ObMap, HomMap} <: FinDomFunctor{Dom,Codom}
  ob_map::ObMap
  hom_map::HomMap
  dom::Dom
  codom::Codom
end

function FinDomFunctor(ob_map::Union{AbstractVector,AbstractDict},
                       hom_map::Union{AbstractVector,AbstractDict},
                       dom::FinCat, codom::Cat)
  # FIXME: Disable checks for dicts due to `DataMigration` issue above.
  ob_map isa AbstractDict || length(ob_map) == length(ob_generators(dom)) ||
    error("Length of object map $ob_map does not match domain $dom")
  hom_map isa AbstractDict || length(hom_map) == length(hom_generators(dom)) ||
    error("Length of morphism map $hom_map does not match domain $dom")

  ob_map = mappairs(x -> functor_key(dom, x), y -> ob(codom, y), ob_map)
  hom_map = mappairs(f -> functor_key(dom, f), g -> hom(codom, g), hom_map)
  FinDomFunctorMap(ob_map, hom_map, dom, codom)
end
FinDomFunctor(ob_map::Union{AbstractVector{Ob},AbstractDict{<:Any,Ob}},
              hom_map::Union{AbstractVector{Hom},AbstractDict{<:Any,Hom}},
              dom::FinCat) where {Ob,Hom} =
  FinDomFunctor(ob_map, hom_map, dom, TypeCat(Ob, Hom))

functor_key(C::FinCat, x) = x
functor_key(C::FinCat, expr::GATExpr) = head(expr) == :generator ?
  first(expr) : error("Functor must be defined on generators")

function Categories.do_compose(F::FinDomFunctorMap, G::FinDomFunctorMap)
  FinDomFunctorMap(mapvals(x -> ob_map(G, x), F.ob_map),
                   mapvals(f -> hom_map(G, f), F.hom_map), dom(F), codom(G))
end

""" Functor object and morphism maps given as vectors.
"""
const FinDomFunctorVector{Dom<:FinCat,Codom<:Cat,
                          ObMap<:AbstractVector,HomMap<:AbstractVector} =
  FinDomFunctorMap{Dom,Codom,ObMap,HomMap}

ob_map(F::FinDomFunctorVector, x::Integer) = F.ob_map[x]
hom_map(F::FinDomFunctorVector, f::Integer) = F.hom_map[f]

collect_ob(F::FinDomFunctorVector) = F.ob_map
collect_hom(F::FinDomFunctorVector) = F.hom_map

Ob(F::FinDomFunctorVector) = FinDomFunction(F.ob_map, Ob(codom(F)))

""" Functor with object and morphism maps given as dictionaries.
"""
const FinDomFunctorDict{Dom<:FinCat,Codom<:Cat,ObKey,HomKey,
                        ObMap<:AbstractDict{ObKey},HomMap<:AbstractDict{HomKey}} =
  FinDomFunctorMap{Dom,Codom,ObMap,HomMap}

ob_map(F::FinDomFunctorDict{Dom,Codom,ObKey}, x::ObKey) where
  {Dom,Codom,ObKey} = F.ob_map[x]
hom_map(F::FinDomFunctorDict{Dom,Codom,ObKey,HomKey}, f::HomKey) where
  {Dom,Codom,ObKey,HomKey} = F.hom_map[f]

# C-set interop
#--------------

function FinDomFunctor(pres::Presentation, X::ACSet)
  ob_map = Dict(c => FinSet(X, nameof(c)) for c in generators(pres, :Ob))
  hom_map = Dict(f => FinFunction(X, nameof(f)) for f in generators(pres, :Hom))
  FinDomFunctor(ob_map, hom_map,
                FinCat(pres), TypeCat(FinSet{Int}, FinFunction{Int}))
end

# Free diagram interop
#---------------------

function FreeDiagram(F::FinDomFunctor{<:FreeCatGraph,<:TypeCat{Ob,Hom}}) where {Ob,Hom}
  diagram = FreeDiagram{Ob,Hom}()
  copy_parts!(diagram, graph(dom(F)))
  diagram[:ob] = collect_ob(F)
  diagram[:hom] = collect_hom(F)
  diagram
end

function FinDomFunctor(diagram::FreeDiagram)
  g = Graph()
  copy_parts!(g, diagram)
  FinDomFunctor(ob(diagram), hom(diagram), FinCat(g))
end

limit(F::FinDomFunctor) = limit(FreeDiagram(F))
colimit(F::FinDomFunctor) = colimit(FreeDiagram(F))

# Natural transformations
#########################

""" A natural transformation whose domain category is finitely generated.

This type is for natural transformations ``α: F ⇒ G: C → D`` such that the
domain category ``C`` is finitely generated. Such a natural transformation is
given by a finite amount of data (one morphism in ``D`` for each generating
object of ``C``) and its naturality is verified by finitely many equations (one
equation for each generating morphism of ``C``).
"""
const FinTransformation{C<:FinCat,D<:Cat,Dom<:FinDomFunctor{C,D},Codom<:FinDomFunctor{C,D}} =
  Transformation{C,D,Dom,Codom}

FinTransformation(F, G; components...) = FinTransformation(components, F, G)

""" Components of a natural transformation.
"""
components(α::FinTransformation) = α.components

""" Is the transformation between `FinDomFunctors` a natural transformation?

This function uses the fact that to check whether a transformation is natural,
it suffices to check the naturality equations on a generating set of morphisms
of the domain category. In some cases, checking the equations may be expensive
or impossible. When the keyword argument `check_equations` is `false`, only the
domains and codomains of the components are checked.

See also: [`is_functorial`](@ref).
"""
function is_natural(α::FinTransformation; check_equations::Bool=true)
  F, G = dom(α), codom(α)
  C, D = dom(F), codom(F) # == dom(G), codom(G)
  all(ob_generators(C)) do c
    α_c = α[c]
    dom(D, α_c) == ob_map(F,c) && codom(D, α_c) == ob_map(G,c)
  end || return false

  if check_equations
    all(hom_generators(C)) do f
      Ff, Gf = hom_map(F,f), hom_map(G,f)
      α_c, α_d = α[dom(C,f)], α[codom(C,f)]
      is_hom_equal(D, compose(D, α_c, Gf), compose(D, Ff, α_d))
    end || return false
  end

  true
end

function check_transformation_domains(F::Functor, G::Functor)
  (C = dom(F)) == dom(G) ||
    error("Mismatched domains in functors $F and $G")
  (D = codom(F)) == codom(G) ||
    error("Mismatched codomains in functors $F and $G")
  (C, D)
end

# Mapping-based transformations
#------------------------------

""" Natural transformation with components given by explicit mapping.
"""
@auto_hash_equals struct FinTransformationMap{C<:FinCat,D<:Cat,
    Dom<:FinDomFunctor{C,D},Codom<:FinDomFunctor{C,D},Comp} <:
    FinTransformation{C,D,Dom,Codom}
  components::Comp
  dom::Dom
  codom::Codom
end

function FinTransformation(components::Union{AbstractVector,AbstractDict},
                           F::FinDomFunctor, G::FinDomFunctor)
  C, D = check_transformation_domains(F, G)
  length(components) == length(ob_generators(C)) ||
    error("Incorrect number of components in $components for domain category $C")
  components = mappairs(x -> transformation_key(C,x), f -> hom(D,f), components)
  FinTransformationMap(components, F, G)
end

transformation_key(C::FinCat, x) = x
transformation_key(C::FinCat, expr::GATExpr) = head(expr) == :generator ?
  first(expr) : error("Natural transformation must be defined on generators")

component(α::FinTransformationMap{C,D,F,G,Comp}, c::Integer) where
  {C,D,F,G,Comp<:AbstractVector} = α.components[c]
component(α::FinTransformationMap{C,D,F,G,Comp}, c::Key) where
  {Key,C,D,F,G,Comp<:AbstractDict{Key}} = α.components[c]
component(α::FinTransformationMap, expr::GATExpr) =
  component(α, first(expr))

function Categories.do_compose(α::FinTransformationMap, β::FinTransformation)
  F = dom(α)
  D = codom(F)
  FinTransformationMap(mapvals(α.components, keys=true) do c, f
                         compose(D, f, component(β, c))
                       end, F, codom(β))
end

function Categories.do_composeH(F::FinDomFunctorMap, β::Transformation)
  G, H = dom(β), codom(β)
  FinTransformationMap(mapvals(c -> component(β, c), F.ob_map),
                       compose(F, G), compose(F, H))
end

function Categories.do_composeH(α::FinTransformationMap, H::Functor)
  F, G = dom(α), codom(α)
  FinTransformationMap(mapvals(f -> hom_map(H, f), α.components),
                       compose(F, H), compose(G, H))
end

# Dict utilities
################

# Something like this should be built into Julia, but unfortunately isn't.

function mappairs(kmap, vmap, pairs::T) where T<:AbstractDict
  (dicttype(T))(kmap(k) => vmap(v) for (k,v) in pairs)
end
mappairs(kmap, vmap, vec::AbstractVector) = map(vmap, vec)

function mapvals(f, pairs::T; keys::Bool=false) where T<:AbstractDict
  (dicttype(T))(if keys
    (k => f(k,v) for (k,v) in pairs)
  else
    (k => f(v) for (k,v) in pairs)
  end)
end
mapvals(f, vec::AbstractVector; keys::Bool=false) =
  keys ? map(f, eachindex(vec), vec) : map(f, vec)

dicttype(::Type{T}) where T <: AbstractDict = T.name.wrapper
dicttype(::Type{<:Iterators.Pairs}) = Dict


end
