include("sketchgat.jl");
include("findmodel.jl");
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra
#------------------------------------------------
# Tests
#------------------------------------------------

if 1+1==1 # don't run these automatically

    G,H = Graph(4), Graph(4)
    add_edges!(G,[1,2,4,4,3],[2,4,3,3,2])
    add_edges!(H,[2,3,1,4,4],[1,1,4,3,3])
    """Create n copies of a CSet based on a graph schema"""
    function init_graphs(schema::CSet, consts::Vector{Int}, n::Int=2)::Vector{CSet}
        cset = graph_to_cset(schema)()
        for (i, con) in enumerate(consts)
            add_parts!(cset, Symbol("x$i"), con)
        end
        return [deepcopy(cset) for _ in 1:n]
    end
    """Confirm canonical hash tracks with whether two CSets are iso"""
    function test_iso(a::CSet,b::CSet, eq::Bool=true)::Test.Pass
        tst = a -> eq ? a : !a
        @test tst(is_isomorphic(a,b))
        @test a != b
        @test tst(canonical_hash(a) == canonical_hash(b))
    end

    G,H = init_graphs(Triangle,[2,2,2])
    for i in 1:3 set_subpart!(G, Symbol("e$i"), [1,1]) end
    for i in 1:3 set_subpart!(H, Symbol("e$i"), [2,2]) end
    test_iso(G,H)

    G,H = init_graphs(Loop, [3])
    set_subpart!(G, Symbol("e1"), [3,2,1])
    set_subpart!(H, Symbol("e1"), [1,3,2])
    test_iso(G,H)

    cyclel, cycler = Graph(3), Graph(3)
    add_edges!(cyclel,[1,2,3],[2,3,1])
    add_edges!(cycler,[3,2,1],[2,1,3])
    test_iso(cyclel, cycler)

    # Example from Hartke and Radcliffe exposition of Nauty
    G,H = Graph(9), Graph(9)
    add_edges!(G,[1,1,2,2,3,3,4,4,5,6,7,8],
                 [7,8,5,6,6,8,5,7,9,9,9,9])
    add_edges!(H,[1,1,3,3,7,7,9,9,2,4,6,8],
                 [2,4,8,6,6,2,4,8,5,5,5,5])
    test_iso(G,H)

    # Same thing as generic CSet
    G,H = init_graphs(GraphG, [12,9])
    set_subpart!(G, Symbol("e1"), [1,1,2,2,3,3,4,4,5,6,7,8]) # srcG
    set_subpart!(G, Symbol("e2"), [7,8,5,6,6,8,5,7,9,9,9,9]) # tgtG
    set_subpart!(H, Symbol("e1"), [1,1,3,3,7,7,9,9,2,4,6,8]) # srcH
    set_subpart!(H, Symbol("e2"), [2,4,8,6,6,2,4,8,5,5,5,5]) # tgtH
    test_iso(G,H)

    q1 = diagram_to_query(nn_prod[1])
    q2 = diagram_to_query(u_monic[1])
    xg = graph_to_cset(SimpleGraphG)()
    for i in 1:3 add_parts!(xg, Symbol("x$i"), 3) end
    for i in 1:6 set_subpart!(xg, Symbol("e$i"), [3,3,3]) end
    q3 = @relation (x1_1=x1_1, x1_2=x1_2) begin
        x1(_id=x1_1)
        x1(_id=x1_2)
    end
    @test length(query(xg,q3))==9


# TEST DIAGRAM TO QUERY
r = diagram_to_query(id(Triangle))

rel = @relation (x1_1=x1_1,x2_2=x2_2,x3_3=x3_3) begin
 x1(_id=x1_1, e1=x2_2, e2=x3_3)
 x2(_id=x2_2, e3=x3_3)
 x3(_id=x3_3)
end
@test is_isomorphic(r, rel)

tri = graph_to_cset(Triangle)()
for i in 1:3 add_parts!(tri, Symbol("x$i"), 2) end
for i in 1:3 set_subpart!(tri, Symbol("e$i"), [1,2]) end
res = query(tri, rel)
for i in 1:2
    @test res[i] == (x1_1=i,x2_2=i,x3_3=i)
end

# TEST PATHS TO QUERY
xgraph = Graph(4) # two paths that meet up but intersect along the way
add_edges!(xgraph, [1,2,1,2,4],[2,3,2,4,3])
xg = graph_to_cset(xgraph)()
for i in 1:4 add_parts!(xg, Symbol("x$i"), 2) end
for (i, p) in enumerate([[1,2],[2,1],[2,1],[2,1],[2,2]])
    set_subpart!(xg, Symbol("e$i"),p)
end

p1 = [1,2]  # (12)→(12)→(21)  # pen1 = 1;2, last1 = 2;1
p2 = [3,4,5] # (12)→(21)→(12)→(22) # pen2 = 1;2, last2=2;2
q = paths_to_query(xgraph, p1, p2)
rel = @relation (pen1=p_1_1,pen2=p_2_2,last1=p_1_2,last2=p_2_3) begin
 x1(_id=init, e1=p_1_1, e3=p_2_1)
 x2(_id=p_1_1, e2=p_1_2)
 x2(_id=p_2_1, e4=p_2_2)
 x4(_id=p_2_2, e5=p_2_3)
end
@test is_isomorphic(q, rel)

# Empty path test
xg = graph_to_cset(Loop)()
add_parts!(xg, Symbol("x1"), 3)
set_subpart!(xg, Symbol("e1"), [2,1,3])
q = paths_to_query(Loop, [1],Int[])
rel = @relation (pen1=init,pen2=init,last1=p_1_1,last2=init) begin
 x1(_id=init, e1=p_1_1)
end
@test is_isomorphic(q, rel)

G = to_combinatorial(Model(SetPermSketch.G, [2]))
@test color_refine(G)[:Elem] == [2,2,1,1,1,1]


G,H = init_graphs(SetPermSketch.G, [2])
set_subpart!(G, :e1, [2,1])
set_subpart!(G, :e2, [2,1])
set_subpart!(H, :e1, [1,1])
set_subpart!(H, :e2, [2,2])
test_iso(G,H,false)

n_perm = [1,2,3,5] # (1) / (21) / (123) / (123)(45)+(1234)(5)
for (n, n_p) in enumerate(n_perm)
 @test length(find_models(SetPermSketch, [n])) == n_p;
end

# Check to/from combinatorial yields isomorphic results
m = Model([1, 1], [1, 2], IntDisjointSets[
    IntDisjointSets{Int64}([3, 4, 3, 4], [0, 0, 1, 1], 2),
    IntDisjointSets{Int64}([1, 2, 3, 4], [0, 0, 0, 0], 4)],
    [[1, 4], [3, 1]], [[1, 2], [1, 2]], Vector{Set{Int64}}[
        [Set([2, 1]), Set()], [Set(), Set([2, 1])]]);
c = to_combinatorial(m);
mc = from_combinatorial(c);
cmc = to_combinatorial(mc);
@test is_isomorphic(c,cmc)

end

#mono_res = find_models(MonoSketch, Dict([2=>2])) # ID and swap, not tt or ff
include("findmodel.jl");

Model(MonoSketch,Dict([2=>3]))
get_nums(CatSketch, Dict([1=>2,2=>3]))