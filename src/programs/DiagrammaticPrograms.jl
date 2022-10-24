""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the standard category-theoretic sense, not
string diagram or wiring diagram. DSLs for constructing wiring diagrams are
provided by other submodules.
"""
module DiagrammaticPrograms
export @graph, @fincat, @finfunctor, @diagram, @free_diagram,
  @migrate, @migration

using Base.Iterators: repeated
using MLStyle: @match

using ...GAT, ...Present, ...Graphs, ...CategoricalAlgebra
using ...Theories: munit
using ...CategoricalAlgebra.FinCats: mapvals, make_map
using ...CategoricalAlgebra.DataMigrations: ConjQuery, GlueQuery, GlucQuery
import ...CategoricalAlgebra.FinCats: FinCat, vertex_name, vertex_named,
  edge_name, edge_named

# Abstract syntax
#################

""" Abstract syntax trees for category and diagram DSLs.
"""
module AST
using MLStyle

abstract type ObExpr end
abstract type HomExpr end
abstract type AssignExpr end

@data DiagramExpr begin
  ObOver(name::Symbol, over::Union{ObExpr,Nothing})
  HomOver(name::Union{Symbol,Nothing}, src::Symbol, tgt::Symbol, over::HomExpr)
  AssignLiteral(name::Symbol, value)
end

@data CatExpr <: DiagramExpr begin
  Ob(name::Symbol)
  Hom(name::Union{Symbol,Nothing}, src::Symbol, tgt::Symbol)
  HomEq(lhs::HomExpr, rhs::HomExpr)
end

@data CatDefinition begin
  Cat(statements::Vector{<:CatExpr})
  Diagram(statements::Vector{<:DiagramExpr})
end

@data ObExpr begin
  ObGenerator(name)
  OnlyOb()
  Apply(ob::ObExpr, hom::HomExpr)
  Coapply(hom::HomExpr, ob::ObExpr)
end
@data LimitExpr <: ObExpr begin
  Limit(statements::Vector{<:DiagramExpr})
  Product(statements::Vector{ObOver})
  Terminal()
end
@data ColimitExpr <: ObExpr begin
  Colimit(statements::Vector{<:DiagramExpr})
  Coproduct(statements::Vector{ObOver})
  Initial()
end

@data HomExpr begin
  HomGenerator(name)
  Compose(homs::Vector{<:HomExpr})
  Id(ob::ObExpr)
  Mapping(assignments::Vector{<:AssignExpr})
end

@data AssignExpr begin
  ObAssign(lhs::Union{ObGenerator,OnlyOb}, rhs::ObExpr)
  HomAssign(lhs::HomGenerator, rhs::HomExpr)
end

function ob_over_pairs(expr::Union{Diagram,ObExpr})
  @match expr begin
    Diagram(statements) || Limit(statements) || Colimit(statements) =>
      (ob.name => ob.over for ob in statements if ob isa AST.ObOver)
    Product(statements) || Coproduct(statements) =>
      (ob.name => ob.over for ob in statements)
    Terminal() || Initial() => ()
  end
end

function hom_over_pairs(expr::Union{Diagram,ObExpr})
  @match expr begin
    Diagram(statements) || Limit(statements) || Colimit(statements) =>
      (hom.name => (hom.src => hom.tgt)
       for hom in statements if hom isa AST.HomOver)
    _ => ()
  end
end

end # AST module

# Graphs
########

@present SchNamedGraph <: SchGraph begin
  VName::AttrType
  EName::AttrType
  vname::Attr(V, VName)
  ename::Attr(E, EName)
end

""" Abstract type for graph with named vertices and edges.
"""
@abstract_acset_type AbstractNamedGraph <: AbstractGraph

""" Graph with named vertices and edges.

The default graph type used by [`@graph`](@ref), [`@fincat`](@ref),
[`@diagram`](@ref), and related macros.
"""
@acset_type NamedGraph(SchNamedGraph, index=[:src,:tgt,:ename],
                       unique_index=[:vname]) <: AbstractNamedGraph
# FIXME: The edge name should also be uniquely indexed, but this currently
# doesn't play nicely with nullable attributes.

vertex_name(g::AbstractNamedGraph, args...) = subpart(g, args..., :vname)
edge_name(g::AbstractNamedGraph, args...) = subpart(g, args..., :ename)

vertex_named(g::AbstractNamedGraph, name) = only(incident(g, name, :vname))
edge_named(g::AbstractNamedGraph, name)= only(incident(g, name, :ename))

""" Construct a graph in a simple, declarative style.

The syntax is reminiscent of Graphviz. Each line a declares a vertex or set of
vertices, or an edge. For example, the following defines a directed triangle:

```julia
@graph begin
  v0, v1, v2
  fst: v0 → v1
  snd: v1 → v2
  comp: v0 → v2
end
```

Vertices in the graph must be uniquely named, whereas edges names are optional.
"""
macro graph(graph_type, body)
  ast = AST.Cat(parse_diagram_ast(body))
  :(parse_graph($(esc(graph_type)), $ast))
end
macro graph(body)
  ast = AST.Cat(parse_diagram_ast(body))
  :(parse_graph(NamedGraph{Symbol,Union{Symbol,Nothing}}, $ast))
end

function parse_graph(::Type{G}, ast::AST.Cat) where
    {G <: HasGraph}
  g = G()
  foreach(stmt -> parse!(g, stmt), ast.statements)
  return g
end

parse!(g::HasGraph, ob::AST.Ob) = add_vertex!(g, vname=ob.name)

function parse!(g::HasGraph, hom::AST.Hom)
  e = add_edge!(g, vertex_named(g, hom.src), vertex_named(g, hom.tgt))
  if has_subpart(g, :ename)
    g[e,:ename] = hom.name
  end
  return e
end

# Categories
############

struct FinCatData{G<:HasGraph}
  graph::G
  equations::Vector{Pair}
end

FinCat(C::FinCatData) = isempty(C.equations) ? FinCat(C.graph) :
  FinCat(C.graph, C.equations)

""" Present a category by generators and relations.

The result is a finitely presented category (`FinCat`) represented by a graph,
possibly with path equations. For example, the simplex category truncated to one
dimension is:

```julia
@fincat begin
  V, E
  (δ₀, δ₁): V → E
  σ₀: E → V

  σ₀ ∘ δ₀ == id(V)
  σ₀ ∘ δ₁ == id(V)
end
```

The objects and morphisms must be uniquely named.
"""
macro fincat(body)
  ast = AST.Cat(parse_diagram_ast(body))
  :(parse_category(NamedGraph{Symbol,Symbol}, $ast))
end

function parse_category(::Type{G}, ast::AST.Cat) where
    {G <: HasGraph}
  cat = FinCatData(G(), Pair[])
  foreach(stmt -> parse!(cat, stmt), ast.statements)
  FinCat(cat)
end

parse!(C::FinCatData, stmt) = parse!(C.graph, stmt)
parse!(C::FinCatData, eq::AST.HomEq) =
  push!(C.equations, parse_path(C.graph, eq.lhs) => parse_path(C.graph, eq.rhs))

function parse_path(g::HasGraph, expr::AST.HomExpr)
  @match expr begin
    AST.HomGenerator(f::Symbol) => Path(g, edge_named(g, f))
    AST.Compose(args) => mapreduce(arg -> parse_path(g, arg), vcat, args)
    AST.Id(AST.ObGenerator(x::Symbol)) => empty(Path, g, vertex_named(g, x))
  end
end

# Functors
##########

""" Define a functor between two finitely presented categories.

Such a functor is defined by sending the object and morphism generators of the
domain category to generic object and morphism expressions in the codomain
category. For example, the following functor embeds the schema for graphs into
the schema for circular port graphs by ignoring the ports:

```julia
@finfunctor SchGraph SchCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
```
"""
macro finfunctor(dom_cat, codom_cat, body)
  # Cannot parse Julia expr during expansion because domain category is needed.
  :(parse_functor($(esc(dom_cat)), $(esc(codom_cat)), $(Meta.quot(body))))
end

function parse_functor(C::FinCat, D::FinCat, ast::AST.Mapping)
  ob_map, hom_map = make_ob_hom_maps(C, ast)
  F = FinFunctor(mapvals(x -> parse_ob(D, x), ob_map),
                 mapvals(f -> parse_hom(D, f), hom_map), C, D)
  is_functorial(F, check_equations=false) ||
    error("Parsed functor is not functorial: $ast")
  return F
end
parse_functor(C::FinCat, D::FinCat, body::Expr) =
  parse_functor(C, D, parse_mapping_ast(body, C))
parse_functor(C::Presentation, D::Presentation, args...) =
  parse_functor(FinCat(C), FinCat(D), args...)

function make_ob_hom_maps(C::FinCat, ast::AST.Mapping; allow_missing::Bool=false,
                          missing_ob::Bool=false, missing_hom::Bool=false)
  allow_missing && (missing_ob = missing_hom = true)
  ob_assign = Dict(a.lhs.name => a.rhs
                   for a in ast.assignments if a isa AST.ObAssign)
  hom_assign = Dict(a.lhs.name => a.rhs
                    for a in ast.assignments if a isa AST.HomAssign)
  ob_map = make_map(ob_generators(C)) do x
    y = pop!(ob_assign, ob_generator_name(C, x), missing)
    (!ismissing(y) || missing_ob) ? y :
      error("Object $(ob_generator_name(C,x)) is not assigned")
  end
  hom_map = make_map(hom_generators(C)) do f
    g = pop!(hom_assign, hom_generator_name(C, f), missing)
    (!ismissing(g) || missing_hom) ? g :
      error("Morphism $(hom_generator_name(C,f)) is not assigned")
  end
  isempty(ob_assign) || error("Unused object assignment(s): $(keys(ob_assign))")
  isempty(hom_assign) || error("Unused morphism assignment(s): $(keys(hom_assign))")
  (ob_map, hom_map)
end

""" Parse expression for object in a category.
"""
function parse_ob(C::FinCat{Ob,Hom}, expr::AST.ObExpr) where {Ob,Hom}
  @match expr begin
    AST.ObGenerator(name) => @match name begin
      x::Symbol => ob_generator(C, x)
      Expr(:curly, _...) => parse_gat_expr(C, name)::Ob
      _ => error("Invalid object generator $name")
    end
    AST.OnlyOb() => only(ob_generators(C))
  end
end

""" Parse expression for morphism in a category.
"""
function parse_hom(C::FinCat{Ob,Hom}, expr::AST.HomExpr) where {Ob,Hom}
  @match expr begin
    AST.HomGenerator(name) => @match name begin
      f::Symbol => hom_generator(C, f)
      Expr(:curly, _...) => parse_gat_expr(C, name)::Hom
      _ => error("Invalid morphism generator $name")
    end
    AST.Compose(args) => mapreduce(
      arg -> parse_hom(C, arg), (fs...) -> compose(C, fs...), args)
    AST.Id(x) => id(C, parse_ob(C, x))
  end
end

""" Parse GAT expression based on curly braces, rather than parentheses.
"""
function parse_gat_expr(C::FinCat, root_expr)
  pres = presentation(C)
  function parse(expr)
    @match expr begin
      Expr(:curly, head::Symbol, args...) =>
        invoke_term(pres.syntax, head, map(parse, args)...)
      x::Symbol => generator(pres, x)
      _ => error("Invalid GAT expression $root_expr")
    end
  end
  parse(root_expr)
end

# Diagrams
##########

""" A diagram without a codomain category.

An intermediate data representation used internally by the parser for the
[`@diagram`](@ref) and [`@migration`](@ref) macros.
"""
struct DiagramData{T,ObMap,HomMap}
  ob_map::ObMap
  hom_map::HomMap
  shape::FinCat
  params::AbstractDict
end
function DiagramData{T}(ob_map::ObMap, hom_map::HomMap,
                        shape, params=Dict()) where {T,ObMap,HomMap}
  DiagramData{T,ObMap,HomMap}(ob_map, hom_map, shape, params)
end

Diagrams.ob_map(d::DiagramData, x) = d.ob_map[x]
Diagrams.hom_map(d::DiagramData, f) = d.hom_map[f]
Diagrams.shape(d::DiagramData) = d.shape

function Diagrams.Diagram(d::DiagramData{T}, codom) where T
  F = FinDomFunctor(d.ob_map, d.hom_map, d.shape, codom)
  isempty(d.params) ? SimpleDiagram{T}(F) : QueryDiagram{T}(F, d.params)
end

""" Present a diagram in a given category.

Recall that a *diagram* in a category ``C`` is a functor ``F: J → C`` from a
small category ``J`` into ``C``. Given the category ``C``, this macro presents a
diagram in ``C``, i.e., constructs a finitely presented indexing category ``J``
together with a functor ``F: J → C``. This method of simultaneous definition is
often more convenient than defining ``J`` and ``F`` separately, as could be
accomplished by calling [`@fincat`](@ref) and then [`@finfunctor`](@ref).

As an example, the limit of the following diagram consists of the paths of
length two in a graph:

```julia
@diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  (t: e₁ → v)::tgt
  (s: e₂ → v)::src
end
```

Morphisms in the indexing category can be left unnamed, which is convenient for
defining free diagrams (see also [`@free_diagram`](@ref)). For example, the
following diagram is isomorphic to the previous one:

```julia
@diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  (e₁ → v)::tgt
  (e₂ → v)::src
end
```

Of course, unnamed morphisms cannot be referenced by name within the `@diagram`
call or in other settings, which can sometimes be problematic.
"""
macro diagram(cat, body)
  ast = AST.Diagram(parse_diagram_ast(body, free=false))
  :(parse_diagram($(esc(cat)), $ast))
end

""" Present a free diagram in a given category.

Recall that a *free diagram* in a category ``C`` is a functor ``F: J → C`` where
``J`` is a free category on a graph, here assumed finite. This macro is
functionally a special case of [`@diagram`](@ref) but changes the interpretation
of equality expressions. Rather than interpreting them as equations between
morphisms in ``J``, equality expresions can be used to introduce anonymous
morphisms in a "pointful" style. For example, the limit of the following diagram
consists of the paths of length two in a graph:

```julia
@free_diagram SchGraph begin
  v::V
  (e₁, e₂)::E
  tgt(e₁) == v
  src(e₂) == v
end
```

Anonymous objects can also be introduced. For example, the previous diagram is
isomorphic to this one:

```julia
@free_diagram SchGraph begin
  (e₁, e₂)::E
  tgt(e₁) == src(e₂)
end
```

Some care must exercised when defining morphisms between diagrams with anonymous
objects, since they cannot be referred to by name.
"""
macro free_diagram(cat, body)
  ast = AST.Diagram(parse_diagram_ast(body, free=true))
  :(parse_diagram($(esc(cat)), $ast))
end

function parse_diagram(C::FinCat, ast::AST.Diagram)
  d = Diagram(parse_diagram_data(C, ast), C)
  is_functorial(diagram(d), check_equations=false) ||
    error("Parsed diagram is not functorial: $ast")
  return d
end
parse_diagram(pres::Presentation, ast::AST.Diagram) =
  parse_diagram(FinCat(pres), ast)

function parse_diagram_data(C::FinCat, statements::Vector{<:AST.DiagramExpr};
                            type=Any, ob_parser=nothing, hom_parser=nothing)
  isnothing(ob_parser) && (ob_parser = x -> parse_ob(C, x))
  isnothing(hom_parser) && (hom_parser = (f,x,y) -> parse_hom(C,f))
  g, eqs = DiagramGraph(), Pair[]
  F_ob, F_hom, params = [], [], Dict{Int,Any}()
  for stmt in statements
    @match stmt begin
      AST.ObOver(x, X) => begin
        parse!(g, AST.Ob(x))
        push!(F_ob, isnothing(X) ? nothing : ob_parser(X))
      end
      AST.HomOver(f, x, y, h) => begin
        e = parse!(g, AST.Hom(f, x, y))
        X, Y = F_ob[src(g,e)], F_ob[tgt(g,e)]
        push!(F_hom, hom_parser(h, X, Y))
        if isnothing(Y)
          # Infer codomain in base category from parsed hom.
          F_ob[tgt(g,e)] = codom(C, F_hom[end])
        end
      end
      AST.AssignLiteral(x, value) => begin
        v = vertex_named(g, x)
        haskey(params, v) && error("Literal already assigned to $x")
        params[v] = value
      end
      AST.HomEq(lhs, rhs) =>
        push!(eqs, parse_path(g, lhs) => parse_path(g, rhs))
      _ => error("Cannot use statement $stmt in diagram definition")
    end
  end
  J = isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
  DiagramData{type}(F_ob, F_hom, J, params)
end
parse_diagram_data(C::FinCat, ast::AST.Diagram; kw...) =
  parse_diagram_data(C, ast.statements; kw...)

const DiagramGraph = NamedGraph{Symbol,Union{Symbol,Nothing}}

# Data migrations
#################

""" A diagram morphism without a domain or codomain.

Like [`DiagramData`](@ref), this an intermediate data representation used
internally by the parser for the [`@migration`](@ref) macro.
"""
struct DiagramHomData{T,ObMap,HomMap}
  ob_map::ObMap
  hom_map::HomMap
end
DiagramHomData{T}(ob_map::ObMap, hom_map::HomMap) where {T,ObMap,HomMap} =
  DiagramHomData{T,ObMap,HomMap}(ob_map, hom_map)

""" Contravariantly migrate data from one acset to another.

This macro is shorthand for defining a data migration using the
[`@migration`](@ref) macro and then calling the `migrate` function. If the
migration will be used multiple times, it is more efficient to perform these
steps separately, reusing the functor defined by `@migration`.

For more about the syntax and supported features, see [`@migration`](@ref).
"""
macro migrate(tgt_type, src_acset, body)
  quote
    let T = $(esc(tgt_type)), X = $(esc(src_acset))
      migrate(T, X, parse_migration(Presentation(T), Presentation(X),
                                    $(Meta.quot(body))))
    end
  end
end

""" Define a contravariant data migration.

This macro provides a DSL to specify a contravariant data migration from
``C``-sets to ``D``-sets for given schemas ``C`` and ``D``. A data migration is
defined by a functor from ``D`` to a category of queries on ``C``. Thus, every
object of ``D`` is assigned a query on ``C`` and every morphism of ``D`` is
assigned a morphism of queries, in a compatible way. Example usages are in the
unit tests. What follows is a technical reference.

Several categories of queries are supported by this macro:

1. Trivial queries, specified by a single object of ``C``. In this case, the
   macro simply defines a functor ``D → C`` and is equivalent to
   [`@finfunctor`](@ref) or [`@diagram`](@ref).
2. *Conjunctive queries*, specified by a diagram in ``C`` and evaluated as a
   finite limit.
3. *Gluing queries*, specified by a diagram in ``C`` and evaluated as a finite
   colimit. An important special case is *linear queries*, evaluated as a
   finite coproduct.
4. *Gluc queries* (gluings of conjunctive queries), specified by a diagram of
   diagrams in ``C`` and evaluated as a colimit of limits. An important special
   case is *duc queries* (disjoint unions of conjunctive queries), evaluated as
   a coproduct of limits.

The query category of the data migration is not specified explicitly but is
inferred from the queries used in the macro call. Implicit conversion is
performed: trivial queries can be coerced to conjunctive queries or gluing
queries, and conjunctive queries and gluing queries can both be coerced to gluc
queries. Due to the implicit conversion, the resulting functor out of ``D`` has
a single query type and thus a well-defined codomain.

Syntax for the right-hand sides of object assignments is:

- a symbol, giving object of ``C`` (query type: trivial)
- `@product ...` (query type: conjunctive)
- `@unit` (alias: `@terminal`, query type: conjunctive)
- `@join ...` (alias: `@limit`, query type: conjunctive)
- `@cases ...` (alias: `@coproduct`, query type: gluing)
- `@empty` (alias: `@initial`, query type: gluing)
- `@glue ...` (alias: `@colimit`, query type: gluing)

Thes query types supported by this macro generalize the kind of queries familiar
from relational databases. Less familiar is the concept of a morphism between
queries, derived from the concept of a morphism between diagrams in a category.
A query morphism is given by a functor between the diagrams' indexing categories
together with a natural transformation filling a triangle of the appropriate
shape. From a practical standpoint, the most important thing to remember is that
a morphism between conjunctive queries is contravariant with respect to the
diagram shapes, whereas a morphism between gluing queries is covariant. TODO:
Reference for more on this.
"""
macro migration(src_schema, body)
  ast = AST.Diagram(parse_diagram_ast(body))
  :(parse_migration($(esc(src_schema)), $ast))
end
macro migration(tgt_schema, src_schema, body)
  # Cannot parse Julia expr during expansion because target schema is needed.
  :(parse_migration($(esc(tgt_schema)), $(esc(src_schema)), $(Meta.quot(body))))
end

""" Parse a contravariant data migration from a Julia expression.

The process kicked off by this internal function is somewhat complicated due to
the need to coerce queries and query morphisms to a common category. The
high-level steps of this process are:

1. Parse the queries and query morphisms into intermediate representations
   ([`DiagramData`](@ref) and [`DiagramHomData`](@ref)) whose final types are
   not yet determined.
2. Promote the query types to the tightest type encompassing all queries, an
   approach reminiscent of Julia's own type promotion system.
3. Convert all query and query morphisms to this common type, yielding `Diagram`
   and `DiagramHom` instances.
"""
function parse_migration(src_schema::Presentation, ast::AST.Diagram)
  C = FinCat(src_schema)
  d = parse_query_diagram(C, ast.statements)
  diagram(make_query(C, d))
end
function parse_migration(tgt_schema::Presentation, src_schema::Presentation,
                         ast::AST.Mapping)
  D, C = FinCat(tgt_schema), FinCat(src_schema)
  ob_rhs, hom_rhs = make_ob_hom_maps(D, ast, missing_hom=true)
  F_ob = mapvals(expr -> parse_query(C, expr), ob_rhs)
  F_hom = mapvals(hom_rhs, keys=true) do f, expr
    parse_query_hom(C, ismissing(expr) ? AST.Mapping(AST.AssignExpr[]) : expr,
                    F_ob[dom(D,f)], F_ob[codom(D,f)])
  end
  diagram(make_query(C, DiagramData{Any}(F_ob, F_hom, D)))
end
function parse_migration(tgt_schema::Presentation, src_schema::Presentation,
                         body::Expr)
  ast = parse_mapping_ast(body, FinCat(tgt_schema), preprocess=true)
  parse_migration(tgt_schema, src_schema, ast)
end

# Query parsing
#--------------

""" Parse expression defining a query.
"""
function parse_query(C::FinCat, expr::AST.ObExpr)
  @match expr begin
    AST.ObGenerator(x) => ob_generator(C, x)
    AST.Limit(stmts) || AST.Product(stmts) =>
      parse_query_diagram(C, stmts, type=op)
    AST.Colimit(stmts) || AST.Coproduct(stmts) =>
      parse_query_diagram(C, stmts, type=id)
    AST.Terminal() => DiagramData{op}([], [], FinCat(DiagramGraph()))
    AST.Initial() => DiagramData{id}([], [], FinCat(DiagramGraph()))
  end
end
function parse_query_diagram(C::FinCat, stmts::Vector{<:AST.DiagramExpr}; kw...)
  parse_diagram_data(C, stmts;
    ob_parser = X -> parse_query(C,X),
    hom_parser = (f,X,Y) -> parse_query_hom(C,f,X,Y), kw...)
end

""" Parse expression defining a morphism of queries.
"""
function parse_query_hom(C::FinCat{Ob}, expr::AST.HomExpr,
                         ::Ob, ::Union{Ob,Nothing}) where Ob
  parse_hom(C, expr)
end

# Conjunctive fragment.

function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping,
                         d::Union{Ob,DiagramData{op}}, d′::DiagramData{op}) where Ob
  ob_rhs, hom_rhs = make_ob_hom_maps(shape(d′), ast, allow_missing=d isa Ob)
  f_ob = mapvals(ob_rhs, keys=true) do j′, rhs
    parse_diagram_ob_rhs(C, rhs, ob_map(d′, j′), d)
  end
  f_hom = mapvals(rhs -> parse_hom(d, rhs), hom_rhs)
  DiagramHomData{op}(f_ob, f_hom)
end
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping,
                         d::DiagramData{op}, c′::Ob) where Ob
  assign = only(ast.assignments)
  DiagramHomData{op}([parse_diagram_ob_rhs(C, assign.rhs, c′, d)], [])
end

# Gluing fragment.

function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping, d::DiagramData{id},
                         d′::Union{Ob,DiagramData{op},DiagramData{id}}) where Ob
  ob_rhs, hom_rhs = make_ob_hom_maps(shape(d), ast,
                                     allow_missing=!(d′ isa DiagramData{id}))
  f_ob = mapvals(ob_rhs, keys=true) do j, rhs
    parse_diagram_ob_rhs(C, rhs, ob_map(d, j), d′)
  end
  f_hom = mapvals(rhs -> parse_hom(d′, rhs), hom_rhs)
  DiagramHomData{id}(f_ob, f_hom)
end
function parse_query_hom(C::FinCat{Ob}, ast::AST.Mapping,
                         c::Union{Ob,DiagramData{op}}, d′::DiagramData{id}) where Ob
  assign = only(ast.assignments)
  DiagramHomData{id}([parse_diagram_ob_rhs(C, assign.rhs, c, d′)], [])
end

function parse_diagram_ob_rhs(C::FinCat, expr, X, Y)
  @match expr begin
    AST.Apply(AST.OnlyOb(), f_expr) =>
      (missing, parse_query_hom(C, f_expr, Y, X))
    AST.Apply(j_expr, f_expr) => let j = parse_ob(Y, j_expr)
      (j, parse_query_hom(C, f_expr, ob_map(Y, j), X))
    end
    AST.Coapply(f_expr, AST.OnlyOb()) =>
      (missing, parse_query_hom(C, f_expr, X, Y))
    AST.Coapply(f_expr, j_expr) => let j = parse_ob(Y, j_expr)
      (j, parse_query_hom(C, f_expr, X, ob_map(Y, j)))
    end
    _ => parse_ob(Y, expr)
  end
end

parse_ob(d::DiagramData, expr::AST.ObExpr) = parse_ob(shape(d), expr)
parse_hom(d::DiagramData, expr::AST.HomExpr) = parse_hom(shape(d), expr)

parse_ob(C, ::Missing) = missing
parse_hom(C, ::Missing) = missing

# Query construction
#-------------------

function make_query(C::FinCat{Ob}, data::DiagramData{T}) where {T, Ob}
  F_ob, F_hom, J = data.ob_map, data.hom_map, shape(data)
  F_ob = mapvals(x -> make_query(C, x), F_ob)
  query_type = mapreduce(typeof, promote_query_type, values(F_ob), init=Ob)
  @assert query_type != Any
  F_ob = mapvals(x -> convert_query(C, query_type, x), F_ob)
  F_hom = mapvals(F_hom, keys=true) do h, f
    make_query_hom(f, F_ob[dom(J,h)], F_ob[codom(J,h)])
  end
  if query_type <: Ob
    Diagram(DiagramData{T}(F_ob, F_hom, J, data.params), C)
  else
    # XXX: Why is the element type of `F_ob` sometimes too loose?
    D = TypeCat(typeintersect(query_type, eltype(values(F_ob))),
                eltype(values(F_hom)))
    @assert isempty(data.params)
    Diagram(DiagramData{T}(F_ob, F_hom, J), D)
  end
end

make_query(C::FinCat{Ob}, x::Ob) where Ob = x

function make_query_hom(f::DiagramHomData{op}, d::Diagram{op}, d′::Diagram{op})
  f_ob = mapvals(f.ob_map, keys=true) do j′, x
    x = @match x begin
      ::Missing => only_ob(shape(d))
      (::Missing, g) => (only_ob(shape(d)), g)
      _ => x
    end
    @match x begin
      (j, g) => Pair(j, make_query_hom(g, ob_map(d, j), ob_map(d′, j′)))
      j => j
    end
  end
  f_hom = mapvals(h -> ismissing(h) ? only_hom(shape(d)) : h, f.hom_map)
  DiagramHom{op}(f_ob, f_hom, d, d′)
end

function make_query_hom(f::DiagramHomData{id}, d::Diagram{id}, d′::Diagram{id})
  f_ob = mapvals(f.ob_map, keys=true) do j, x
    x = @match x begin
      ::Missing => only_ob(shape(d′))
      (::Missing, g) => (only_ob(shape(d′)), g)
      _ => x
    end
    @match x begin
      (j′, g) => Pair(j′, make_query_hom(g, ob_map(d, j), ob_map(d′, j′)))
      j′ => j′
    end
  end
  f_hom = mapvals(h -> ismissing(h) ? only_hom(shape(d′)) : h, f.hom_map)
  DiagramHom{id}(f_ob, f_hom, d, d′)
end

function make_query_hom(f::Hom, d::Diagram{T,C}, d′::Diagram{T,C}) where
    {T, Ob, Hom, C<:FinCat{Ob,Hom}}
  cat = codom(diagram(d))
  munit(DiagramHom{T}, cat, f, dom_shape=shape(d), codom_shape=shape(d′))
end
make_query_hom(f, x, y) = f

only_ob(C::FinCat) = only(ob_generators(C))
only_hom(C::FinCat) = (@assert is_discrete(C); id(C, only_ob(C)))

# Query promotion
#----------------

# Promotion of query types is modeled loosely on Julia's type promotion system:
# https://docs.julialang.org/en/v1/manual/conversion-and-promotion/

promote_query_rule(::Type, ::Type) = Union{}
promote_query_rule(::Type{<:ConjQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  ConjQuery{C}
promote_query_rule(::Type{<:GlueQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  GlueQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:Ob}) where {Ob,C<:FinCat{Ob}} =
  GlucQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:ConjQuery{C}}) where C =
  GlucQuery{C}
promote_query_rule(::Type{<:GlucQuery{C}}, ::Type{<:GlueQuery{C}}) where C =
  GlucQuery{C}

promote_query_type(T, S) = promote_query_result(
  T, S, Union{promote_query_rule(T,S), promote_query_rule(S,T)})
promote_query_result(T, S, ::Type{Union{}}) = typejoin(T, S)
promote_query_result(T, S, U) = U

convert_query(::FinCat, ::Type{T}, x::S) where {T, S<:T} = x

function convert_query(cat::C, ::Type{<:Diagram{T,C}}, x::Ob) where
  {T, Ob, C<:FinCat{Ob}}
  g = NamedGraph{Symbol,Symbol}(1, vname=nameof(x))
  munit(Diagram{T}, cat, x, shape=FinCat(g))
end
function convert_query(::C, ::Type{<:GlucQuery{C}}, d::ConjQuery{C}) where C
  munit(Diagram{id}, TypeCat(ConjQuery{C}, Any), d)
end
function convert_query(cat::C, ::Type{<:GlucQuery{C}}, d::GlueQuery{C}) where C
  J = shape(d)
  new_ob = make_map(ob_generators(J)) do j
    convert_query(cat, ConjQuery{C}, ob_map(d, j))
  end
  new_hom = make_map(hom_generators(J)) do h
    munit(Diagram{op}, cat, hom_map(d, h),
          dom_shape=new_ob[dom(J,h)], codom_shape=new_ob[codom(J,h)])
  end
  Diagram{id}(FinDomFunctor(new_ob, new_hom, J))
end
function convert_query(cat::C, ::Type{<:GlucQuery{C}}, x::Ob) where
    {Ob, C<:FinCat{Ob}}
  convert_query(cat, GlucQuery{C}, convert_query(cat, ConjQuery{C}, x))
end

# Julia expression to AST
#########################

""" Parse category or diagram from Julia expression to AST.
"""
function parse_diagram_ast(body::Expr; free::Bool=false, preprocess::Bool=true)
  if preprocess
    body = reparse_arrows(body)
  end
  state = DiagramASTState()
  stmts = mapreduce(vcat, statements(body), init=AST.CatExpr[]) do expr
    @match expr begin
      # X
      X::Symbol => [AST.Ob(X)]
      # X, Y, ...
      Expr(:tuple, Xs...) => map(AST.Ob, Xs)
      # X → Y
      Expr(:call, :(→), X::Symbol, Y::Symbol) => [AST.Hom(nothing, X, Y)]
      # f : X → Y
      Expr(:call, :(:), f::Symbol, Expr(:call, :(→), X::Symbol, Y::Symbol)) =>
        [AST.Hom(f, X, Y)]
      # (f, g, ...) : X → Y
      Expr(:call, (:), Expr(:tuple, fs...),
           Expr(:call, :(→), X::Symbol, Y::Symbol)) =>
        map(f -> AST.Hom(f, X, Y), fs)
      # x => X
      # x::X
      Expr(:call, :(=>), x::Symbol, X) || Expr(:(::), x::Symbol, X) =>
        [push_ob_over!(state, AST.ObOver(x, parse_ob_ast(X)))]
      # (x, y, ...) => X
      # (x, y, ...)::X
      Expr(:call, :(=>), Expr(:tuple, xs...), X) ||
      Expr(:(::), Expr(:tuple, xs...), X) => let ob = parse_ob_ast(X)
        map(x -> push_ob_over!(state, AST.ObOver(x, ob)), xs)
      end
      # (f: x → y) => h
      # (f: x → y)::h
      Expr(:call, :(=>), Expr(:call, :(:), f::Symbol,
                              Expr(:call, :(→), x::Symbol, y::Symbol)), h) ||
      Expr(:(::), Expr(:call, :(:), f::Symbol,
      Expr(:call, :(→), x::Symbol, y::Symbol)), h) => begin
        X, Y = state.ob_over[x], state.ob_over[y]
        [AST.HomOver(f, x, y, parse_hom_ast(h, X, Y))]
      end
      # (x → y) => h
      # (x → y)::h
      Expr(:call, :(=>), Expr(:call, :(→), x::Symbol, y::Symbol), h) ||
      Expr(:(::), Expr(:call, :(→), x::Symbol, y::Symbol), h) => begin
        X, Y = state.ob_over[x], state.ob_over[y]
        [AST.HomOver(nothing, x, y, parse_hom_ast(h, X, Y))]
      end
      # x == "foo"
      # "foo" == x
      Expr(:call, :(==), x::Symbol, value::Literal) ||
      Expr(:call, :(==), value::Literal, x::Symbol) =>
        [AST.AssignLiteral(x, get_literal(value))]
      # h(x) == y
      # y == h(x)
      (Expr(:call, :(==), call::Expr, y::Symbol) ||
       Expr(:call, :(==), y::Symbol, call::Expr)) && if free end => begin
         h, x = destructure_unary_call(call)
         X, Y = state.ob_over[x], state.ob_over[y]
         [AST.HomOver(nothing, x, y, parse_hom_ast(h, X, Y))]
      end
      # h(x) == "foo"
      # "foo" == h(x)
      (Expr(:call, :(==), call::Expr, value::Literal) ||
       Expr(:call, :(==), value::Literal, call::Expr)) && if free end => begin
         (h, x), y = destructure_unary_call(call), gen_anon!(state)
         X = state.ob_over[x]
         [AST.ObOver(y, nothing),
          AST.AssignLiteral(y, get_literal(value)),
          AST.HomOver(nothing, x, y, parse_hom_ast(h, X))]
      end
      # h(x) == k(y)
      Expr(:call, :(==), lhs::Expr, rhs::Expr) && if free end => begin
        (h, x), (k, y) = destructure_unary_call(lhs), destructure_unary_call(rhs)
        z = gen_anon!(state)
        X, Y = state.ob_over[x], state.ob_over[y]
        # Assumes that codomain not needed to parse morphisms.
        [AST.ObOver(z, nothing),
         AST.HomOver(nothing, x, z, parse_hom_ast(h, X)),
         AST.HomOver(nothing, y, z, parse_hom_ast(k, Y))]
      end
      # f == g
      Expr(:call, :(==), lhs, rhs) && if !free end =>
        [AST.HomEq(parse_hom_ast(lhs), parse_hom_ast(rhs))]
      ::LineNumberNode => AST.CatExpr[]
      _ => error("Cannot parse statement in category/diagram definition: $expr")
    end
  end
end

Base.@kwdef mutable struct DiagramASTState
  nanon::Int = 0
  ob_over::Dict{Symbol,AST.ObExpr} = Dict{Symbol,AST.ObExpr}()
end
gen_anon!(state::DiagramASTState) = Symbol("##unnamed#$(state.nanon += 1)")

function push_ob_over!(state::DiagramASTState, ob::AST.ObOver)
  isnothing(ob.name) && return ob
  haskey(state.ob_over, ob.name) &&
    error("Object with name $ob has already been defined")
  state.ob_over[ob.name] = ob.over
  return ob
end

""" Parse object expression from Julia expression to AST.
"""
function parse_ob_ast(expr)::AST.ObExpr
  @match expr begin
    Expr(:macrocall, _...) => parse_ob_macro_ast(expr)
    x::Symbol || Expr(:curly, _...) => AST.ObGenerator(expr)
    _ => error("Invalid object expression $expr")
  end
end
const compose_ops = (:(⋅), :(⨟), :(∘))

function parse_ob_macro_ast(expr)::AST.ObExpr
  @match expr begin
    Expr(:macrocall, form, ::LineNumberNode, args...) =>
      parse_ob_macro_ast(Expr(:macrocall, form, args...))
    Expr(:macrocall, &(Symbol("@limit")), body) ||
    Expr(:macrocall, &(Symbol("@join")), body) =>
      AST.Limit(parse_diagram_ast(body, free=true, preprocess=false))
    Expr(:macrocall, &(Symbol("@product")), body) =>
      AST.Product(parse_diagram_ast(body, free=true, preprocess=false))
    Expr(:macrocall, &(Symbol("@terminal"))) ||
    Expr(:macrocall, &(Symbol("@unit"))) =>
      AST.Terminal()
    Expr(:macrocall, &(Symbol("@colimit")), body) ||
    Expr(:macrocall, &(Symbol("@glue")), body) =>
      AST.Colimit(parse_diagram_ast(body, free=true, preprocess=false))
    Expr(:macrocall, &(Symbol("@coproduct")), body) ||
    Expr(:macrocall, &(Symbol("@cases")), body) =>
      AST.Coproduct(parse_diagram_ast(body, free=true, preprocess=false))
    Expr(:macrocall, &(Symbol("@initial"))) ||
    Expr(:macrocall, &(Symbol("@empty"))) =>
      AST.Initial()
    _ => error("Invalid object macro $expr")
  end
end

""" Parse morphism expression from Julia expression to AST.
"""
function parse_hom_ast(expr, dom::Union{AST.ObGenerator,Nothing}=nothing,
                       codom::Union{AST.ObGenerator,Nothing}=nothing)
  # Domain and codomain are not used, but may be supplied for uniformity.
  @match expr begin
    Expr(:call, :compose, args...) => AST.Compose(map(parse_hom_ast, args))
    Expr(:call, :(⋅), f, g) || Expr(:call, :(⨟), f, g) =>
      AST.Compose([parse_hom_ast(f), parse_hom_ast(g)])
    Expr(:call, :(∘), f, g) => AST.Compose([parse_hom_ast(g), parse_hom_ast(f)])
    Expr(:call, :id, x) => AST.Id(parse_ob_ast(x))
    f::Symbol || Expr(:curly, _...) => AST.HomGenerator(expr)
    _ => error("Invalid morphism expression $expr")
  end
end

# Limit fragment.
function parse_hom_ast(expr, dom::AST.LimitExpr, cod::AST.LimitExpr)
  parse_mapping_ast((args...) -> parse_apply_ast(args..., dom), expr, cod)
end
function parse_hom_ast(expr, dom::AST.ObGenerator, cod::AST.LimitExpr)
  parse_mapping_ast(expr, cod) do (args...)
    AST.Apply(AST.OnlyOb(), parse_hom_ast(args..., dom))
  end
end
function parse_hom_ast(expr, dom::AST.LimitExpr, cod::AST.ObGenerator)
  [AST.ObAssign(AST.OnlyOb(), parse_apply_ast(expr, cod, dom))] |> AST.Mapping
end

# Colimit fragment.
function parse_hom_ast(expr, dom::AST.ColimitExpr, cod::AST.ColimitExpr)
  parse_mapping_ast((args...) -> parse_coapply_ast(args..., cod), expr, dom)
end
function parse_hom_ast(expr, dom::Union{AST.ObGenerator,AST.LimitExpr},
                       cod::AST.ColimitExpr)
  [AST.ObAssign(AST.OnlyOb(), parse_coapply_ast(expr, dom, cod))] |> AST.Mapping
end
function parse_hom_ast(expr, dom::AST.ColimitExpr,
                       cod::Union{AST.ObGenerator,AST.LimitExpr})
  parse_mapping_ast(expr, dom) do (args...)
    AST.Coapply(parse_hom_ast(args..., cod), AST.OnlyOb())
  end
end

""" Parse object/morphism mapping from Julia expression to AST.
"""
function parse_mapping_ast(f_parse_ob_assign, body, dom; preprocess::Bool=false)
  if preprocess
    body = reparse_arrows(body)
  end
  ob_map = Dict{Symbol,AST.ObExpr}()
  get_ob(x) = get(ob_map, x) do
    error("Morphism assigned before assigning (co)domain $x")
  end
  dom_obs, dom_homs = Dict(ob_over_pairs(dom)), Dict(hom_over_pairs(dom))
  stmts = mapreduce(vcat, statements(body), init=AST.AssignExpr[]) do expr
    @match expr begin
      # lhs => rhs
      Expr(:call, :(=>), lhs::Symbol, rhs) => begin
        if lhs ∈ keys(dom_obs)
          x, X = lhs, dom_obs[lhs]
          ob_map[x] = x′ = f_parse_ob_assign(rhs, X)
          [AST.ObAssign(AST.ObGenerator(x), x′)]
        elseif lhs ∈ keys(dom_homs)
          f, (x, y) = lhs, dom_homs[lhs]
          x′, y′ = get_ob(x), get_ob(y)
          f′ = parse_hom_ast(rhs, x′, y′)
          [AST.HomAssign(AST.HomGenerator(f), f′)]
        else
          error("$lhs is not the name of an object or morphism generator")
        end
      end
      # (lhs, lhs′, ...) => rhs
      Expr(:call, :(=>), Expr(:tuple, lhs...), rhs) => begin
        if all(∈(keys(dom_obs)), lhs)
          X = only(unique(dom_obs[x] for x in lhs))
          x′ = f_parse_ob_assign(rhs, X)
          for x in lhs; ob_map[x] = x′ end
          map(x -> AST.ObAssign(AST.ObGenerator(x), x′), lhs)
        elseif all(∈(keys(dom_homs)), lhs)
          x′, y′ = only(unique(
            (let (x,y) = dom_homs[f]; get_ob(x) => get_ob(y) end for f in lhs)))
          f′ = parse_hom_ast(rhs, x′, y′)
          map(f -> AST.HomAssign(AST.HomGenerator(f), f′), lhs)
        else
          error("$lhs are not all names of object or morphism generators")
        end
      end
      ::LineNumberNode => AST.AssignExpr[]
      _ => error("Cannot parse object or morphism assignment: $expr")
    end
  end
  AST.Mapping(stmts)
end
function parse_mapping_ast(body, dom; kw...)
  parse_mapping_ast((rhs, _) -> parse_ob_ast(rhs), body, dom; kw...)
end

function parse_apply_ast(expr, X, target)
  y::Symbol, f = @match expr begin
    ::Symbol => (expr, nothing)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(⋅), :(⨟)), all_ops=compose_ops)
    Expr(:call, name::Symbol, _) => reverse(destructure_unary_call(expr))
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  isnothing(f) && return AST.ObGenerator(y)
  Y = only(Y′ for (y′,Y′) in ob_over_pairs(target) if y == y′)
  AST.Apply(AST.ObGenerator(y), parse_hom_ast(f, Y, X))
end

function parse_coapply_ast(expr, X, target)
  y::Symbol, f = @match expr begin
    ::Symbol => (expr, nothing)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(∘),), all_ops=compose_ops)
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  isnothing(f) && return AST.ObGenerator(y)
  Y = only(Y′ for (y′,Y′) in ob_over_pairs(target) if y == y′)
  AST.Coapply(parse_hom_ast(f, X, Y), AST.ObGenerator(y))
end

ob_over_pairs(expr) = AST.ob_over_pairs(expr)
ob_over_pairs(C::FinCat) =
  (ob_generator_name(C,x) => nothing for x in ob_generators(C))

hom_over_pairs(expr) = AST.hom_over_pairs(expr)
hom_over_pairs(C::FinCat) = begin
  (hom_generator_name(C,f) =>
    (ob_generator_name(C,dom(C,f)) => ob_generator_name(C,codom(C,f)))
   for f in hom_generators(C))
end

# Julia expression utilities
############################

# Types that can be Julia literals.
const Literal = Union{Number,Char,String,QuoteNode}

get_literal(value::Literal) = value
get_literal(node::QuoteNode) = node.value::Symbol

statements(expr) = (expr isa Expr && expr.head == :block) ? expr.args : [expr]

""" Reparse Julia expressions for function/arrow types.

In Julia, `f : x → y` is parsed as `(f : x) → y` instead of `f : (x → y)`.
"""
function reparse_arrows(expr)
  @match expr begin
    Expr(:call, :(→), Expr(:call, :(:), f, x), y) =>
      Expr(:call, :(:), f, Expr(:call, :(→), x, y))
    Expr(head, args...) => Expr(head, (reparse_arrows(arg) for arg in args)...)
    _ => expr
  end
end

""" Left-most argument plus remainder of left-associated binary operations.
"""
function leftmost_arg(expr, ops; all_ops=nothing)
  isnothing(all_ops) && (all_ops = ops)
  function leftmost(expr)
    @match expr begin
      Expr(:call, op2, Expr(:call, op1, x, y), z) &&
          if op1 ∈ all_ops && op2 ∈ all_ops end => begin
        x, rest = leftmost(Expr(:call, op1, x, y))
        (x, Expr(:call, op2, rest, z))
      end
      Expr(:call, op, x, y) && if op ∈ ops end => (x, y)
      _ => (nothing, expr)
    end
  end
  leftmost(expr)
end

""" Destructure Julia expression `:(f(g(x)))` to `(:(f∘g), :x)`, for example.
"""
function destructure_unary_call(expr::Expr)
  @match expr begin
    Expr(:call, head, x::Symbol) => (head, x)
    Expr(:call, head, arg) => begin
      rest, x = destructure_unary_call(arg)
      (Expr(:call, :(∘), head, rest), x)
    end
  end
end

end
