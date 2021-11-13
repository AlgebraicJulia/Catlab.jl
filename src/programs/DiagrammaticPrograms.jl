""" DSLs for defining categories, diagrams, and related structures.

Here "diagram" means diagram in the standard category-theoretic sense, not
string diagram or wiring diagram. DSLs for constructing wiring diagrams are
provided by other submodules.
"""
module DiagrammaticPrograms
export @graph, @fincat, @finfunctor, @diagram, @migration

using Base.Iterators: repeated
using MLStyle: @match

using ...Present, ...Graphs, ...CategoricalAlgebra
using ...Theories: munit
using ...CategoricalAlgebra.FinCats: mapvals, make_map
using ...CategoricalAlgebra.DataMigrations: ConjQuery, GlueQuery, GlucQuery
import ...CategoricalAlgebra.DataMigrations: ob_name, hom_name, ob_named, hom_named
using ...Graphs.BasicGraphs: TheoryGraph

# Data types
############

@present TheoryNamedGraph <: TheoryGraph begin
  Name::AttrType
  vname::Attr(V, Name)
  ename::Attr(E, Name)
end

""" Default graph type for [`@fincat`](@ref) macro and related macros.
"""
@acset_type NamedGraph(TheoryNamedGraph, index=[:src,:tgt],
                       unique_index=[:vname,:ename]) <: AbstractGraph

@present TheoryMaybeNamedGraph <: TheoryGraph begin
  VName::AttrType
  EName::AttrType
  vname::Attr(V, VName)
  ename::Attr(E, EName)
end

@acset_type _MaybeNamedGraph(TheoryMaybeNamedGraph, index=[:src,:tgt],
                             unique_index=[:vname]) <: AbstractGraph

""" Default graph type for [`@graph`](@ref) macro.

Vertex names are uniquely indexed and edge names are optional and unindexed.
"""
const MaybeNamedGraph{Name} = _MaybeNamedGraph{Name,Union{Nothing,Name}}

vertex_name(g::HasGraph, args...) = subpart(g, args..., :vname)
edge_name(g::HasGraph, args...) = subpart(g, args..., :ename)

vertex_named(g::HasGraph, name) = incident(g, name, :vname)
edge_named(g::HasGraph, name)= incident(g, name, :ename)

# Graphs
########

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

Vertices in the graph must be uniquely named, whereas edges names are optional
and need not be unique.
"""
macro graph(graph_type, body)
  :(parse_graph($(esc(graph_type)), $(Meta.quot(body))))
end
macro graph(body)
  :(parse_graph(MaybeNamedGraph{Symbol}, $(Meta.quot(body))))
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
      _ => error("@graph macro cannot parse line: $stmt")
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
  parse_category(NamedGraph{Symbol}, body)
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
      _ => error("@fincat macro cannot parse line: $stmt")
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
  F = FinFunctor(mapvals(x -> ob_named(D, x), ob_rhs),
                 mapvals(f -> parse_hom(D, f), hom_rhs), C, D)
  is_functorial(F, check_equations=false) ||
    error("Result of @finfunctor macro is not functorial: $body")
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
    get(assignments, ob_name(C, x)) do
      allow_missing ? missing : error("Object $(ob_name(C,x)) is not assigned")
    end
  end
  hom_rhs = make_map(hom_generators(C)) do f
    get(assignments, hom_name(C, f)) do
      allow_missing ? missing : error("Morphism $(hom_name(C,f)) is not assigned")
    end
  end
  (ob_rhs, hom_rhs)
end

""" Parse expression for morphism in a category.
"""
function parse_hom(C::FinCat, expr)
  function parse(expr)
    @match expr begin
      Expr(:call, :compose, args...) =>
        mapreduce(parse, (fs...) -> compose(C, fs...), args)
      Expr(:call, :(⋅), f, g) ||
      Expr(:call, :(⨟), f, g) => compose(C, parse(f), parse(g))
      Expr(:call, :(∘), f, g) => compose(C, parse(g), parse(f))
      Expr(:call, :id, x::Symbol) => id(C, ob_named(C, x))
      f::Symbol => hom_named(C, f)
      _ => error("Invalid morphism expression $expr")
    end
  end
  parse(expr)
end

ob_name(C::FinCatGraph{<:NamedGraph}, x) = vertex_name(graph(C), x)
hom_name(C::FinCatGraph{<:NamedGraph}, f) = edge_name(graph(C), f)
ob_named(C::FinCatGraph{<:NamedGraph}, name) = vertex_named(graph(C), name)
hom_named(C::FinCatGraph{<:NamedGraph}, name) = edge_named(graph(C), name)

# Diagrams
##########

""" Present a diagram in a given category.

Recall that a *diagram* in a category ``C`` is a functor ``F: J → C`` from a
small category ``J`` into ``C``. Given the category ``C``, this macro presents a
diagram in ``C``, i.e., constructs a finitely presented indexing category ``J``
together with a functor ``F: J → C``. This method of simultaneous definition is
often more convenient than defining ``J`` and ``F`` separately.

For example, the following diagram specifies the paths of length two in a graph:

```julia
@diagram FinCat(TheoryGraph) begin
  v::V
  (e1, e2)::E
  (t: e1 → v)::tgt
  (s: e2 → v)::src
end
```
"""
macro diagram(cat, body)
  :(parse_diagram($(esc(cat)), $(Meta.quot(body))))
end

function parse_diagram(C::FinCat, body::Expr; kw...)
  F_ob, F_hom, J = parse_diagram_data(
    x -> ob_named(C,x), (f,x,y) -> parse_hom(C,f), body; kw...)
  F = FinFunctor(F_ob, F_hom, J, C)
  is_functorial(F, check_equations=false) ||
    error("@diagram macro defined diagram that is not functorial: $body")
  return F
end
parse_diagram(pres::Presentation, body::Expr; kw...) =
  parse_diagram(FinCat(pres), body; kw...)

function parse_diagram_data(parse_ob, parse_hom, body::Expr;
                            preprocess::Bool=true)
  g, eqs = NamedGraph{Symbol}(), Pair[]
  F_ob, F_hom = [], []
  if preprocess
    body = reparse_arrows(body)
  end
  for stmt in statements(body)
    @match stmt begin
      # x => X
      Expr(:call, :(=>), x::Symbol, X) ||
      # x::X
      Expr(:(::), x::Symbol, X) => begin
        add_vertex!(g, vname=x)
        push!(F_ob, parse_ob(X))
      end
      # (x, y, ...) => X
      Expr(:call, :(=>), Expr(:tuple, xs...), X) ||
      # (x, y, ...)::X
      Expr(:(::), Expr(:tuple, xs...), X) => begin
        add_vertices!(g, length(xs), vname=xs)
        append!(F_ob, repeated(parse_ob(X), length(xs)))
      end
      # (f: x → y) => h
      Expr(:call, :(=>), Expr(:call, :(:), f::Symbol,
                              Expr(:call, :(→), x::Symbol, y::Symbol)), h) ||
      # (f: x → y)::h
      Expr(:(::), Expr(:call, :(:), f::Symbol,
                       Expr(:call, :(→), x::Symbol, y::Symbol)), h) => begin
        e = parse_edge!(g, x, y, ename=f)
        push!(F_hom, parse_hom(h, F_ob[src(g,e)], F_ob[tgt(g,e)]))
      end
      # f == g
      Expr(:call, :(==), lhs, rhs) => push!(eqs, parse_path_equation(g, lhs, rhs))
      ::LineNumberNode => nothing
      _ => error("@diagram macro cannot parse line: $stmt")
    end
  end
  J = isempty(eqs) ? FinCat(g) : FinCat(g, eqs)
  (F_ob, F_hom, J)
end

# Data migrations
#################

""" A diagram without a codomain category.

Internal data type used by parser in [`@migration`](@ref) macro.
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

Internal data type used by parser in [`@migration`](@ref) macro.
"""
struct DiagramHomData{T,ObMap,HomMap}
  ob_map::ObMap
  hom_map::HomMap

  function DiagramHomData{T}(ob_map::ObMap, hom_map::HomMap) where {T,ObMap,HomMap}
    new{T,ObMap,HomMap}(ob_map, hom_map)
  end
end

""" Define a data migration query.

This macro provides a DSL to specify a data migration query from a ``C``-set to
a ``D``-set for arbitrary schemas ``C`` and ``D``.
"""
macro migration(src_schema, body)
  :(parse_migration($(esc(src_schema)), $(Meta.quot(body))))
end
macro migration(tgt_schema, src_schema, body)
  :(parse_migration($(esc(tgt_schema)), $(esc(src_schema)), $(Meta.quot(body))))
end

function parse_migration(src_schema::Presentation, body::Expr;
                         preprocess::Bool=true)
  C = FinCat(src_schema)
  F_ob, F_hom, J = parse_query_diagram(C, body; preprocess=preprocess)
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
    x::Symbol => ob_named(C, x)
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
    _ => error("@migration macro cannot parse query $expr")
  end
end
function parse_query_diagram(C::FinCat, expr::Expr; preprocess::Bool=false)
  parse_diagram_data(X -> parse_query(C,X), (f,x,y) -> parse_query_hom(C,f,x,y),
                     expr; preprocess=preprocess)
end

""" Parse expression defining a morphism of queries.
"""
function parse_query_hom(C::FinCat{Ob}, expr, ::Ob, ::Ob) where Ob
  parse_hom(C, expr)
end

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
    _ => error("@migration macro cannot parse object assignment $expr")
  end
  j = ob_named(shape(d), j_name)
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
    _ => error("@migration macro cannot parse object assignment $expr")
  end
  j′ = ob_named(shape(d′), j′_name)
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
  f_hom = mapvals(f.hom_map) do h; @match h begin
    ::Missing => only_hom(shape(d))
    _ => h
  end end
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
  f_hom = mapvals(f.hom_map) do h; @match h begin
    ::Missing => only_hom(shape(d′))
    _ => h
  end end
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
  munit(Diagram{T}, cat, x,
        shape=FinCat(NamedGraph{Symbol}(1, vname=nameof(x))))
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

end
