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
using ...Graphs.BasicGraphs: TheoryGraph
import ...CategoricalAlgebra.FinCats: vertex_name, vertex_named,
  edge_name, edge_named

# Graphs
########

@present TheoryNamedGraph <: TheoryGraph begin
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
@acset_type NamedGraph(TheoryNamedGraph, index=[:src,:tgt,:ename],
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
  :(parse_graph($(esc(graph_type)), $(Meta.quot(body))))
end
macro graph(body)
  :(parse_graph(NamedGraph{Symbol,Union{Symbol,Nothing}}, $(Meta.quot(body))))
end

function parse_graph(G::Type, body::Expr; preprocess::Bool=true)
  g = G()
  if preprocess
    body = reparse_arrows(body)
  end
  for stmt in statements(body)
    @match stmt begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # u → v
      Expr(:call, :(→), u::Symbol, v::Symbol) => parse_edge!(g, u, v)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      ::LineNumberNode => nothing
      _ => error("Cannot parse line in graph definition: $stmt")
    end
  end
  return g
end

function parse_edge!(g, s::Symbol, t::Symbol;
                     ename::Union{Symbol,Nothing}=nothing)
  e = add_edge!(g, vertex_named(g, s), vertex_named(g, t))
  if has_subpart(g, :ename)
    g[e,:ename] = ename
  end
  return e
end

function reparse_arrows(expr)
  # `f : x → y` is parsed by Julia as `(f : x) → y`, not `f : (x → y)`.
  @match expr begin
    Expr(:call, :(→), Expr(:call, :(:), f, x), y) =>
      Expr(:call, :(:), f, Expr(:call, :(→), x, y))
    Expr(head, args...) => Expr(head, (reparse_arrows(arg) for arg in args)...)
    _ => expr
  end
end

statements(expr) = (expr isa Expr && expr.head == :block) ? expr.args : [expr]

# Categories
############

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
  parse_category(NamedGraph{Symbol,Symbol}, body)
end

function parse_category(G::Type, body::Expr; preprocess::Bool=true)
  g, eqs = G(), Pair[]
  if preprocess
    body = reparse_arrows(body)
  end
  for stmt in statements(body)
    @match stmt begin
      # v
      v::Symbol => add_vertex!(g, vname=v)
      # u, v, ...
      Expr(:tuple, vs...) => add_vertices!(g, length(vs), vname=vs)
      # e : u → v
      Expr(:call, :(:), e::Symbol, Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        parse_edge!(g, u, v, ename=e)
      # (e, f, ...) : u → v
      Expr(:call, (:), Expr(:tuple, es...), Expr(:call, :(→), u::Symbol, v::Symbol)) =>
        for e in es; parse_edge!(g, u, v, ename=e) end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(eqs, parse_path_equation(g, lhs, rhs))
      ::LineNumberNode => nothing
      _ => error("Cannot parse line in category definition: $stmt")
    end
  end
  isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
end

""" Parse an equation between paths in a named graph.
"""
parse_path_equation(g, lhs, rhs) = parse_path(g, lhs) => parse_path(g, rhs)

""" Parse a path in a named graph.
"""
function parse_path(g, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) => mapreduce(parse, vcat, args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => vcat(parse(f), parse(g))
      Expr(:call, :(∘), f, g) => vcat(parse(g), parse(f))
      Expr(:call, :id, x::Symbol) => empty(Path, g, vertex_named(g, x))
      f::Symbol => Path(g, edge_named(g, f))
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

# Functors
##########

""" Define a functor between two finitely presented categories.

Such a functor is defined by sending the object and morphism generators of the
domain category to generic object and morphism expressions in the codomain
category. For example, the following functor embeds the schema for graphs into
the schema for circular port graphs by ignoring the ports:

```julia
@finfunctor TheoryGraph ThCPortGraph begin
  V => Box
  E => Wire
  src => src ⨟ box
  tgt => tgt ⨟ box
end
```
"""
macro finfunctor(dom_cat, codom_cat, body)
  :(parse_functor($(esc(dom_cat)), $(esc(codom_cat)), $(Meta.quot(body))))
end

function parse_functor(C::FinCat, D::FinCat, body::Expr)
  ob_rhs, hom_rhs = parse_ob_hom_maps(C, body)
  F = FinFunctor(mapvals(x -> parse_ob(D, x), ob_rhs),
                 mapvals(f -> parse_hom(D, f), hom_rhs), C, D)
  is_functorial(F, check_equations=false) ||
    error("Parsed functor is not functorial: $body")
  return F
end
function parse_functor(C::Presentation, D::Presentation, body::Expr; kw...)
  parse_functor(FinCat(C), FinCat(D), body; kw...)
end

function parse_ob_hom_maps(C::FinCat, body::Expr; allow_missing::Bool=false)
  assignments = Dict{Symbol,Union{Expr,Symbol}}()
  assign(lhs, rhs) = if haskey(assignments, lhs)
    error("Left-hand side $lhs assigned twice in $body")
  else
    assignments[lhs] = rhs
  end
  for stmt in statements(body)
    @match stmt begin
      # x => y
      Expr(:call, :(=>), lhs::Symbol, rhs) => assign(lhs, rhs)
      # (x, x′, ...) => y
      Expr(:call, :(=>), Expr(:tuple, args...), rhs) =>
        foreach(lhs -> assign(lhs, rhs), args)
      ::LineNumberNode => nothing
      _ => error("Invalid assignment statement $stmt")
    end
  end
  ob_rhs = make_map(ob_generators(C)) do x
    y = pop!(assignments, ob_generator_name(C, x), missing)
    (!ismissing(y) || allow_missing) ? y :
      error("Object $(ob_generator_name(C,x)) is not assigned")
  end
  hom_rhs = make_map(hom_generators(C)) do f
    g = pop!(assignments, hom_generator_name(C, f), missing)
    (!ismissing(g) || allow_missing) ? g :
      error("Morphism $(hom_generator_name(C,f)) is not assigned")
  end
  isempty(assignments) ||
    error(string("Unused assignment(s): ", join(keys(assignments), ", ")))
  (ob_rhs, hom_rhs)
end

""" Parse expression for object in a category.
"""
function parse_ob(C::FinCat{Ob,Hom}, expr) where {Ob,Hom}
  @match expr begin
    x::Symbol => ob_generator(C, x)
    Expr(:curly, _...) => parse_gat_expr(C, expr)::Ob
    _ => error("Invalid object expression $expr")
  end
end

""" Parse expression for morphism in a category.
"""
function parse_hom(C::FinCat{Ob,Hom}, expr) where {Ob,Hom}
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) =>
        mapreduce(parse, (fs...) -> compose(C, fs...), args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => compose(C, parse(f), parse(g))
      Expr(:call, :(∘), f, g) => compose(C, parse(g), parse(f))
      Expr(:call, :id, x::Symbol) => id(C, ob_generator(C, x))
      f::Symbol => hom_generator(C, f)
      Expr(:curly, _...) => parse_gat_expr(C, expr)::Hom
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
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
@diagram TheoryGraph begin
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
@diagram TheoryGraph begin
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
  :(parse_diagram($(esc(cat)), $(Meta.quot(body))))
end

""" Present a free diagram in a given category.

Recall that a *free diagram* in a category ``C`` is a functor ``F: J → C`` where
``J`` is a free category on a graph, here assumed finite. This macro is
functionally a special case of [`@diagram`](@ref) but, for convenience, changes
the interpretation of equality expressions. Rather than interpreting them as
equations between morphisms in ``J``, equality expresions can be used to
introduce anonymous morphisms in a "pointful" style. For example, the limit of
the following diagram consists of the paths of length two in a graph:

```julia
@free_diagram TheoryGraph begin
  v::V
  (e₁, e₂)::E
  tgt(e₁) == v
  src(e₂) == v
end
```

Anonymous objects can also be introduced. For example, the previous diagram is
isomorphic to this one:

```julia
@free_diagram TheoryGraph begin
  (e₁, e₂)::E
  tgt(e₁) == src(e₂)
end
```

Some care must exercised when defining morphisms between diagrams with anonymous
objects, since they cannot be referred to by name.
"""
macro free_diagram(cat, body)
  :(parse_diagram($(esc(cat)), $(Meta.quot(body)), free=true))
end

function parse_diagram(C::FinCat, body::Expr; kw...)
  F_ob, F_hom, J = parse_diagram_data(
    C, x -> parse_ob(C,x), (f,x,y) -> parse_hom(C,f), body; kw...)
  F = FinFunctor(F_ob, F_hom, J, C)
  is_functorial(F, check_equations=false) ||
    error("Parsed diagram is not functorial: $body")
  return F
end
parse_diagram(pres::Presentation, body::Expr; kw...) =
  parse_diagram(FinCat(pres), body; kw...)

function parse_diagram_data(C::FinCat, parse_ob, parse_hom, body::Expr;
                            free::Bool=false, preprocess::Bool=true)
  g, eqs = NamedGraph{Symbol,Union{Symbol,Nothing}}(), Pair[]
  F_ob, F_hom = [], []
  function push_hom!(h, x, y; name=nothing)
    e = parse_edge!(g, x, y, ename=name)
    push!(F_hom, parse_hom(h, F_ob[src(g,e)], F_ob[tgt(g,e)]))
    return e
  end

  nanon = 0
  if preprocess
    body = reparse_arrows(body)
  end
  for stmt in statements(body)
    @match stmt begin
      # x => X
      # x::X
      Expr(:call, :(=>), x::Symbol, X) || Expr(:(::), x::Symbol, X) => begin
        add_vertex!(g, vname=x)
        push!(F_ob, parse_ob(X))
      end
      # (x, y, ...) => X
      # (x, y, ...)::X
      Expr(:call, :(=>), Expr(:tuple, xs...), X) ||
      Expr(:(::), Expr(:tuple, xs...), X) => begin
        add_vertices!(g, length(xs), vname=xs)
        append!(F_ob, repeated(parse_ob(X), length(xs)))
      end
      # (f: x → y) => h
      # (f: x → y)::h
      Expr(:call, :(=>), Expr(:call, :(:), f::Symbol,
                              Expr(:call, :(→), x::Symbol, y::Symbol)), h) ||
      Expr(:(::), Expr(:call, :(:), f::Symbol,
                       Expr(:call, :(→), x::Symbol, y::Symbol)), h) =>
        push_hom!(h, x, y, name=f)
      # (x → y) => h
      # (x → y)::h
      Expr(:call, :(=>), Expr(:call, :(→), x::Symbol, y::Symbol), h) ||
      Expr(:(::), Expr(:call, :(→), x::Symbol, y::Symbol), h) =>
        push_hom!(h, x, y)
      # h(x) == y
      # y == h(x)
      (Expr(:call, :(==), call::Expr, y::Symbol) ||
       Expr(:call, :(==), y::Symbol, call::Expr)) && if free end =>
         push_hom!(destructure_unary_call(call)..., y)
      # h(x) == k(y)
      Expr(:call, :(==), lhs::Expr, rhs::Expr) && if free end => begin
        (h, x), (k, y) = destructure_unary_call(lhs), destructure_unary_call(rhs)
        z = Symbol("##unnamed#$(nanon += 1)")
        add_vertex!(g, vname=z)
        push!(F_ob, nothing) # Assumes that codomain not needed to parse homs.
        e1, e2 = push_hom!(h, x, z), push_hom!(k, y, z)
        # Infer codomain from parsed homs.
        Z1, Z2 = codom(C, F_hom[e1]), codom(C, F_hom[e2])
        Z1 == Z2 || error("Codomain mismatch in $stmt: $Z1 != $Z2")
        F_ob[end] = Z1
      end
      # f == g
      Expr(:call, :(==), lhs, rhs) && if !free end =>
        push!(eqs, parse_path_equation(g, lhs, rhs))
      ::LineNumberNode => nothing
      _ => error("Cannot parse line in diagram definition: $stmt")
    end
  end
  J = isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
  (F_ob, F_hom, J)
end

# Data migrations
#################

""" A diagram without a codomain category.

An intermediate data representation used internally by the parser for the
[`@migration`](@ref) macro.
"""
struct DiagramData{T,ObMap,HomMap,Shape<:FinCat}
  ob_map::ObMap
  hom_map::HomMap
  shape::Shape

  function DiagramData{T}(ob_map::ObMap, hom_map::HomMap, shape::Shape) where
      {T,ObMap,HomMap,Shape<:FinCat}
    new{T,ObMap,HomMap,Shape}(ob_map, hom_map, shape)
  end
end

Diagrams.ob_map(d::DiagramData, x) = d.ob_map[x]
Diagrams.hom_map(d::DiagramData, f) = d.hom_map[f]
Diagrams.shape(d::DiagramData) = d.shape

""" A diagram morphism without a domain or codomain.

Like [`DiagramData`](@ref), an intermediate data representation used internally
by the parser for the [`@migration`](@ref) macro.
"""
struct DiagramHomData{T,ObMap,HomMap}
  ob_map::ObMap
  hom_map::HomMap

  function DiagramHomData{T}(ob_map::ObMap, hom_map::HomMap) where {T,ObMap,HomMap}
    new{T,ObMap,HomMap}(ob_map, hom_map)
  end
end

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
- `@join ...` (alias: `@limit`, query type: conjunctive)
- `@cases ...` (alias: `@coproduct`, query type: gluing or gluc)
- `@glue ...` (alias: `@colimit`, query type: gluing or gluc)

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
  :(parse_migration($(esc(src_schema)), $(Meta.quot(body))))
end
macro migration(tgt_schema, src_schema, body)
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
function parse_migration(src_schema::Presentation, body::Expr;
                         preprocess::Bool=true)
  C = FinCat(src_schema)
  F_ob, F_hom, J = parse_query_diagram(C, body; free=false, preprocess=preprocess)
  make_migration_functor(F_ob, F_hom, J, C)
end
function parse_migration(tgt_schema::Presentation, src_schema::Presentation,
                         body::Expr; preprocess::Bool=true)
  D, C = FinCat(tgt_schema), FinCat(src_schema)
  if preprocess
    body = reparse_arrows(body)
  end
  ob_rhs, hom_rhs = parse_ob_hom_maps(D, body)
  F_ob = mapvals(expr -> parse_query(C, expr), ob_rhs)
  F_hom = mapvals(hom_rhs, keys=true) do f, expr
    parse_query_hom(C, expr, F_ob[dom(D,f)], F_ob[codom(D,f)])
  end
  make_migration_functor(F_ob, F_hom, D, C)
end

# Query parsing
#--------------

""" Parse expression defining a query.
"""
function parse_query(C::FinCat, expr)
  @match expr begin
    x::Symbol => ob_generator(C, x)
    Expr(:macrocall, form, args...) &&
        if form ∈ (Symbol("@limit"), Symbol("@join")) end => begin
      DiagramData{op}(parse_query_diagram(C, last(args))...)
    end
    Expr(:macrocall, form, args...) &&
        if form == Symbol("@product") end => begin
      d = DiagramData{op}(parse_query_diagram(C, last(args))...)
      is_discrete(shape(d)) ? d : error("Product query is not discrete: $expr")
    end
    Expr(:macrocall, form, args...) &&
        if form ∈ (Symbol("@colimit"), Symbol("@glue")) end => begin
      DiagramData{id}(parse_query_diagram(C, last(args))...)
    end
    Expr(:macrocall, form, args...) &&
        if form ∈ (Symbol("@coproduct"), Symbol("@cases")) end => begin
      d = DiagramData{id}(parse_query_diagram(C, last(args))...)
      is_discrete(shape(d)) ? d : error("Cases query is not discrete: $expr")
    end
    _ => error("Cannot parse query in migration definition: $expr")
  end
end
function parse_query_diagram(C::FinCat, expr::Expr;
                             free::Bool=true, preprocess::Bool=false)
  parse_diagram_data(C, X -> parse_query(C,X),
                     (f,x,y) -> parse_query_hom(C,f,x,y), expr;
                     free=free, preprocess=preprocess)
end

""" Parse expression defining a morphism of queries.
"""
parse_query_hom(C::FinCat{Ob}, expr, ::Ob, ::Union{Ob,Nothing}) where Ob =
  parse_hom(C, expr)

# Conjunctive fragment.

function parse_query_hom(C::FinCat, expr, d::DiagramData{op}, d′::DiagramData{op})
  ob_rhs, hom_rhs = parse_ob_hom_maps(shape(d′), expr)
  f_ob = mapvals(ob_rhs, keys=true) do j′, rhs
    parse_conj_query_ob_rhs(C, rhs, d, ob_map(d′, j′))
  end
  f_hom = mapvals(rhs -> parse_hom(shape(d), rhs), hom_rhs)
  DiagramHomData{op}(f_ob, f_hom)
end
function parse_query_hom(C::FinCat{Ob}, expr, c::Ob, d′::DiagramData{op}) where Ob
  ob_rhs, f_hom = parse_ob_hom_maps(shape(d′), expr, allow_missing=true)
  f_ob = mapvals(ob_rhs, keys=true) do j′, rhs
    ismissing(rhs) ? missing : (missing, parse_query_hom(C, rhs, c, ob_map(d′, j′)))
  end
  @assert all(ismissing, f_hom)
  DiagramHomData{op}(f_ob, f_hom)
end
function parse_query_hom(C::FinCat{Ob}, expr, d::DiagramData{op}, c′::Ob) where Ob
  DiagramHomData{op}([parse_conj_query_ob_rhs(C, expr, d, c′)], [])
end

# Gluing fragment.

function parse_query_hom(C::FinCat, expr, d::DiagramData{id}, d′::DiagramData{id})
  ob_rhs, hom_rhs = parse_ob_hom_maps(shape(d), expr)
  f_ob = mapvals(ob_rhs, keys=true) do j, rhs
    parse_glue_query_ob_rhs(C, rhs, ob_map(d, j), d′)
  end
  f_hom = mapvals(expr -> parse_hom(shape(d′), expr), hom_rhs)
  DiagramHomData{id}(f_ob, f_hom)
end
function parse_query_hom(C::FinCat{Ob}, expr, c::Union{Ob,DiagramData{op}},
                         d′::DiagramData{id}) where Ob
  DiagramHomData{id}([parse_glue_query_ob_rhs(C, expr, c, d′)], [])
end
function parse_query_hom(C::FinCat{Ob}, expr, d::DiagramData{id},
                         c′::Union{Ob,DiagramData{op}}) where Ob
  ob_rhs, f_hom = parse_ob_hom_maps(shape(d), expr, allow_missing=true)
  f_ob = mapvals(ob_rhs, keys=true) do j, rhs
    ismissing(rhs) ? missing : (missing, parse_query_hom(C, rhs, ob_map(d, j), c′))
  end
  @assert all(ismissing, f_hom)
  DiagramHomData{id}(f_ob, f_hom)
end

""" Parse RHS of object assignment in morphism out of conjunctive query.
"""
function parse_conj_query_ob_rhs(C::FinCat, expr, d::DiagramData{op}, c′)
  j_name, f_expr = @match expr begin
    x::Symbol => (x, nothing)
    Expr(:tuple, x::Symbol, f) => (x, f)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(⋅), :(⨟)), all_ops=compose_ops)
    Expr(:call, name::Symbol, _) => reverse(destructure_unary_call(expr))
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  j = ob_generator(shape(d), j_name)
  isnothing(f_expr) ? j :
    (j, parse_query_hom(C, f_expr, ob_map(d, j), c′))
end

""" Parse RHS of object assignment in morphism into gluing query.
"""
function parse_glue_query_ob_rhs(C::FinCat, expr, c, d′::DiagramData{id})
  j′_name, f_expr = @match expr begin
    x::Symbol => (x, nothing)
    Expr(:tuple, x::Symbol, f) => (x, f)
    Expr(:call, op, _...) && if op ∈ compose_ops end =>
      leftmost_arg(expr, (:(∘),), all_ops=compose_ops)
    _ => error("Cannot parse object assignment in migration: $expr")
  end
  j′ = ob_generator(shape(d′), j′_name)
  isnothing(f_expr) ? j′ :
    (j′, parse_query_hom(C, f_expr, c, ob_map(d′, j′)))
end

const compose_ops = (:(⋅), :(⨟), :(∘))

# Query construction
#-------------------

function make_migration_functor(F_ob, F_hom, D::FinCat, C::FinCat)
  diagram(make_query(C, DiagramData{id}(F_ob, F_hom, D)))
end

function make_query(C::FinCat{Ob}, d::DiagramData{T}) where {T, Ob}
  F_ob, F_hom, J = d.ob_map, d.hom_map, shape(d)
  F_ob = mapvals(x -> make_query(C, x), F_ob)
  query_type = mapreduce(typeof, promote_query_type, values(F_ob), init=Ob)
  @assert query_type != Any
  F_ob = mapvals(x -> convert_query(C, query_type, x), F_ob)
  F_hom = mapvals(F_hom, keys=true) do h, f
    make_query_hom(f, F_ob[dom(J,h)], F_ob[codom(J,h)])
  end
  Diagram{T}(if query_type <: Ob
    FinFunctor(F_ob, F_hom, shape(d), C)
  else
    # XXX: Why is the element type of `F_ob` sometimes too loose?
    D = TypeCat(typeintersect(query_type, eltype(values(F_ob))),
                eltype(values(F_hom)))
    FinDomFunctor(F_ob, F_hom, shape(d), D)

  end)
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

# Utilities
###########

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

""" Destructure the expression `:(f(g(x)))` to `(:(f∘g), :x)`, for example.
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
