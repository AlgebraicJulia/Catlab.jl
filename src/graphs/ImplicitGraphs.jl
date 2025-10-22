# TODO interface
module ImplicitGraphs

using ..BasicGraphs

""" An implicit cyclic graph with `n` vertices. The `offset` of an ImplicitGraph tracks the first vertex starts """
abstract type ImplicitGraph end

mutable struct CycleGraph <: ImplicitGraph
    n::Int
    offset::Int
    CycleGraph(n::Int, offset=0) = new(n, offset)
end
export CycleGraph

Graph(g::CycleGraph) = cycle_graph(nv(g))

nv(g::CycleGraph) = g.n
ne(g::CycleGraph) = g.n

mutable struct CompleteGraph <: ImplicitGraph
    n::Int
    offset::Int
    CompleteGraph(n::Int, offset=0) = new(n, offset)
end
export CompleteGraph

Graph(g::CompleteGraph) = complete_graph(nv(g))

nv(g::CompleteGraph) = g.n
ne(g::CompleteGraph) = g.n^2

mutable struct DiscreteGraph <: ImplicitGraph
    n::Int
    offset::Int
    DiscreteGraph(n::Int, offset=0) = new(n, offset)
end
export DiscreteGraph

Graph(g::DiscreteGraph) = Graph(nv(g))

nv(g::DiscreteGraph) = g.n
ne(g::DiscreteGraph) = 0

"""
The Fraisse limit of finite graphs.
"""
struct RadoGraph <: ImplicitGraph end
export RadoGraph

nv(::RadoGraph) = 1:Inf # countable
ne(::RadoGraph) = 1:Inf # countable

# compute this
src(::RadoGraph, e) = missing
tgt(::RadoGraph, e) = missing

""" Checks for an edge between m and n. This requires that `m < n` hold. However, since `n >> m == 0` for all `m >= n`, we don't need to check.
"""
has_edge(::RadoGraph, m::Int, n::Int) = isodd(n >> m) 

struct Neighbors{G <: ImplicitGraph}
    g::G
    v::Int
end

Base.IteratorSize(::Type{Neighbors{RadoGraph}}) = Base.IsInfinite()

function Base.iterate(g::Neighbors{RadoGraph})
    next = g.v + 1
    while !has_edge(g.g, g.v, next)
        next += 1
    end
    (next, next)
end

function Base.iterate(g::Neighbors{RadoGraph}, state)
    next = state + 1
    while !has_edge(g.g, g.v, next)
        next += 1
    end
    (next, next)
end

BasicGraphs.neighbors(g::RadoGraph, v::Int) = Neighbors{RadoGraph}(g, v)
export neighbors

function shift(g::T, n) where T <: ImplicitGraph
    g.offset += n
    g
end

function shift!(g::T, n) where T <: ImplicitGraph
    g.offset += n
end
export shift!

function LabeledGraph(g::T) where T <: ImplicitGraph
    X = Graph(T(g))
    L = LabeledGraph{Int}(nv(g))
    for e in edges(X)
        # TODO would be nice to treat the implict graph like an iterator and generate the edges rather than materialize it as an "explicit" Graph first
        add_part!(L, :E, src=g[e, :src], tgt=g[e, :tgt])
    end
    for v in vertices(L)
        set_subpart!(L, v, :label, v + g.offset)
    end
    return L
end
export LabeledGraph

LabeledGraph(::Type{T}, args...) where T <: ImplicitGraph =
    LabeledGraph(T(args...))

# TODO defined for LabeledGraph

"""    The concatenation of two graphs is their union with index shifting. This operation is symmetric up to relabeling. The matrix representation is block concatenation.
"""
function disjoint_union(G::HasGraph, H::HasGraph)
    X = deepcopy(G)
    vs = add_parts!(X, :V, nv(H))
    offset = vs[1] - 1 # TODO why offset by one?
    for e in edges(H)
        add_edge!(X, src(H, e) + offset, tgt(H, e) + offset)
    end
    X
end
export disjoint_union

disjoint_union(G::HasGraph, H::ImplicitGraph) = disjoint_union(G, Graph(H))
disjoint_union(H::ImplicitGraph, G::HasGraph) = disjoint_union(G, H)

function disjoint_union(args...)::HasGraph
    @assert eltype(args) == Graph
    reduce(disjoint_union, args)
end

"""    The clique union of two graphs is their disjoint union with an additional bidirectional, bicomplete graph. The matrix representation is block concatenation with a fully-connected matrices in the B and C cells.
"""
function clique_union(G::HasGraph, H::HasGraph)
    X = disjoint_union(G, H)
    offset = nv(G)
    for v in vertices(G)
        for w in vertices(H)
            add_edge!(X, v, w + offset)
            add_edge!(X, w + offset, v)
        end
    end
    X
end
export clique_union

clique_union(G::HasGraph, H::ImplicitGraph) = clique_union(G, Graph(H))
clique_union(H::ImplicitGraph, G::HasGraph) = clique_union(G, H)

function clique_union(args...)
    @assert eltype(args) == Graph
    reduce(clique_union, args)
end

# # TODO the right thing to do here is promote this to a DisjointUnion, since the arguments are assumed to be Lazy
# function Base.:+(g::ImplicitGraph, h::ImplicitGraph)
#     disjoint_union(Graph(g), Graph(h))
# end

# forward chain
function chain_union(G::HasGraph, H::HasGraph; offset::Int=0)
    X = disjoint_union(G, H)
    g_offset = nv(G)
    for v in vertices(G)
        v > offset || continue
        for w in vertices(H)
            add_edge!(X, v, w + g_offset)
        end
    end
    X
end

# function cyclic_union(G::Graph, H::Graph)::Graph
#     cyclic_union([G, H])
# end

# # [G1, G2, G3, G4]
# # g12 <- G1.[v >= 1] => G2
# # g23 <- (g12).[v >= offsets[|G1|]] => G3
# # g34 <- (g23).[v >= offsets[|G2|]] => G4...
function cyclic_union(graphs::Vector{HasGraph})::HasGraph
    nvs = [0; accumulate(+, nv.(graphs))...]
    chain = foldl(enumerate(graphs)) do (idx, fst), (_, snd)
        chain_union(fst, snd; offset=nvs[idx])
    end
    # loop back around
    for v in vertices(chain)
        v > nvs[end-1] || continue
        for w in vertices(graphs[1])
            add_edge!(chain, v, w)
        end
    end
    chain
end
export cyclic_union
# \circlearrowright

cyclic_union(G::HasGraph, H::ImplicitGraph) = cyclic_union(G, Graph(H))
cyclic_union(H::ImplicitGraph, G::HasGraph) = cyclic_union(G, H)

end
