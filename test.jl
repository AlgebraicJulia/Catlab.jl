
include("modelfind.jl");
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra

# LIMIT EXAMPLE 
# Two function α⇉β and their pullback f×ᵦg
G = Graph(3);
add_edges!(G, [1,1,3,3],[2,2,1,1]); # 1=f 2=g 3=π₁ 4=π₂
cone_dia=Graph(4);
add_edges!(cone_dia, [1,3,4,4],[2,2,1,3]); # ASSUMING LAST IND IS APEX
cone_T = T(cone_dia, G, V=[1,2,1,3], E=[1,2,3,4]);
fls = FLS(G, T[T(Graph(0), G) for _ in 1:3], 
             T[cone_T]);
apextabs, bases, legdatas = cone_data(fls);
ig = init_grph(fls.G, [2,2,2]);
diagram_cset, start = diagram_data(fls);
srch = consts -> [clean(r, [:α,:β,Symbol("f×ᵦg")],[:f,:g,:π₁,:π₂]) 
                  for r in search(fls, consts)]

# The pullback is empty because no f=[1,1] and g=[2,2]
@test length(srch([2,2,0])) == 1

# There are 4 models. 
# f=[1,2], g=[1,2] means the pullback is (1,1),(2,2)
# f=[1,2], g=[1,1] means the pullback is (1,1),(1,2)
# f=[1,1], g=[1,2] means the pullback is (1,1),(2,1)
# f=[2,1], g=[1,2] means the pullback is (1,2),(2,1)
@test length(srch([2,2,2]))==4

# If f,g map to same element, then pullback is A×A
@test length(srch([2,2,4]))==1

# DIAGRAM EXAMPLE
# Two sets A&B, where A has an identity function
# and B has an involution. There is an f:A->B with
# a right inverse g:B->A. Thus f is a monomorphism.
G = Graph(2); # 1=A, 2=B
add_edges!(G, [1,1,2,2],[1,2,1,2]); # 1=id, 2=f, 3=g, 4=inv
dia1,dia2 = Graph(2), Graph(2);
add_edges!(dia1,[1,1,2],[1,2,1]); #equal paths starting from A
add_edges!(dia2,[1,2],[2,1]);     #equal paths starting from B
fls=FLS(G, T[T(dia1,G,V=[1,2],E=[1,2,3]),
             T(dia2,G,V=[2,2],E=[4,4])], T[]);
srch = consts -> [clean(r, [:A,:B],[:id,:f,:g,:inv]) for r in search(fls, consts)]
# inv can be swap or id, f is forced to be an iso
@test length(srch([2,2])) == 2
# inv can be swap or id, f's choices are symmetric.
@test length(srch([2,1])) == 2

# There are 4 nonisomorphic options for A=2,B=3:
# inv can be id OR swap 2 of the three elements in B.
# There is only one automorph where inv is id, and
# if B swaps, then f(1) and f(2) can map to the swapped
# elements, in which case there is just one automorph.
# There are two automorphs in the case where only one out of
# f(1),f(2) is in the swapped pair in B. These are
# distinguished by whether or not the element of g that is
# not mapped to maps to the A whose image in in the swap or not.
@test length(srch([2,3]))==4


@present TheoryLI(FreeSchema) begin
    (A, B, Apk, Bpk)::Ob
    a::Hom(A,Apk)
    b::Hom(B,Bpk)
    aid::Hom(A,Apk)
    inv::Hom(B, Bpk)
    f::Hom(A,Bpk)
    g::Hom(B,Apk)
end;
const LI = CSetType(TheoryLI, index=[:f,:g,:aid,:a,:b,:inv]);

cset_2_2 = @acset LI begin
    A = 8
    B = 8
    Apk = 2
    Bpk = 2
    a = [1,1,1,1,2,2,2,2]
    b = [1,1,1,1,2,2,2,2]
    aid = [1,2,1,2,1,2,1,2]
    inv = [1,2,1,2,1,2,1,2]
    f = [1,1,2,2,1,1,2,2]
    g = [1,1,2,2,1,1,2,2]
end;

diagram_cset = @acset LI begin
    A = 1
    B = 3
    Apk = 3 
    Bpk = 4
    a = [1]
    b = [1,3,4]
    aid = [1]
    inv = [2,4,3]
    f = [1]
    g = [1,2,3]
end;

start = Dict([:A=>1,:B=>2]) # which Ob is the "start"
PKs = [:a, :b]
obs = [:A, :B]
legdatas = Dict{Symbol, Vector{Tuple{Int64, Symbol}}}[] # which objects are legs, and what are the arrows from the apex
apextabs = [:C]

res = search(cset_2_2, diagram_cset, start, PKs, obs, CSet[], legdatas, apextabs)

############################################################
@present TheoryLim(FreeSchema) begin
    (A, B, C, Apk, Bpk,Cpk)::Ob
    a::Hom(A,Apk)
    b::Hom(B,Bpk)
    c::Hom(C,Cpk)
    f::Hom(A,Bpk)
    g::Hom(A,Bpk)
    c1::Hom(C,Apk)
    c2::Hom(C,Apk)
end;
const LL = CSetType(TheoryLim, index=[:f,:g,:c1,:c2,:a,:b,:c]);
cset224 = @acset LL begin
    Apk = 2
    Bpk = 2
    Cpk = 2
    A = 8
    B = 2
    C = 8
    a = [1,1,1,1,2,2,2,2]
    c = [1,1,1,1,2,2,2,2]
    b = [1,2]
    f = [1,2,1,2,1,2,1,2]
    g = [1,1,2,2,1,1,2,2]
    c1 = [1,2,1,2,1,2,1,2]
    c2 = [1,1,2,2,1,1,2,2]
end;

llsol = @acset LL begin
    Apk = 2
    Bpk = 2
    Cpk = 2
    A = 2
    B = 2
    C = 2
    a = [1,2]
    c = [1,2]
    b = [1,2]
    f = [1,2]
    g = [2,1]
    c1 = [1,2]
    c2 = [2,1]
end;


# Trivial diagram
diagram_cset = @acset LL begin
    Apk = 3
    Bpk = 3
    Cpk = 1
    A = 1
    B = 1
    C = 1
    a=[1]
    b=[1]
    c=[1]
    f=[2]
    g=[3]
    c1=[2]
    c2=[3]
end;

base_dia = @acset LL begin 
    Apk = 2  # x1pk
    Bpk = 3  # x2pk 
    Cpk = 0
    A = 2    # x1
    a = [1,2]
    f = [1,3]
    g = [2,1]
end 

start = Dict([:A=>1,:B=>1,:C=>1]);
PKs = [:a, :b, :c];
obs = [:A, :B, :C];
legdatas = [Dict([:A=>[(1,:c1),(2,:c2)]])]; # which objects are legs, and what are the arrows from the apex
apextabs = [:C];
bases = CSet[base_dia];
start = Dict([:A=>1,:B=>1, :C=>1]); # which Ob is the "start"

guess = choose(cset224, :C, 1,3);
ghash = canonical_hash(guess);

guess2 = choose(cset224, :A, 1,3);

res = search(llsol, diagram_cset, start,
             PKs, obs, bases,
             legdatas, apextabs)

########################
# OLD WORLD #
############################
find_models(MonoSketch, [1,2]) # works
# m = find_models(ReflSketch, [2,3]); # works, but takes a VERY long time
# find_models(NatNumSketch, [1,1]) # works
find_models(ReflSketch, [2,3])

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


if 1+1==1
G,H = init_graphs(Triangle,[2,2,2]);
for i in 1:3 set_subpart!(G, Symbol("e$i"), [1,1]) end
for i in 1:3 set_subpart!(H, Symbol("e$i"), [2,2]) end

modtrip = to_cset(from_cset(G, true),Triangle, true)
@test is_isomorphic(modtrip, G)

G,H = init_graphs(Loop, [3]);
set_subpart!(G, Symbol("e1"), [3,2,1])
set_subpart!(H, Symbol("e1"), [1,3,2])
test_iso(G,H)

cyclel, cycler = Graph(3), Graph(3);
add_edges!(cyclel,[1,2,3],[2,3,1]);
add_edges!(cycler,[3,2,1],[2,1,3]);
test_iso(cyclel, cycler);



# Example from Hartke and Radcliffe exposition of Nauty
G,H = Graph(9), Graph(9);
add_edges!(G,[1,1,2,2,3,3,4,4,5,6,7,8],
                [7,8,5,6,6,8,5,7,9,9,9,9])
add_edges!(H,[1,1,3,3,7,7,9,9,2,4,6,8],
                [2,4,8,6,6,2,4,8,5,5,5,5])
test_iso(G,H);

# Same thing as generic CSet
G,H = init_graphs(GraphG, [12,9]);
set_subpart!(G, Symbol("e1"), [1,1,2,2,3,3,4,4,5,6,7,8]); # srcG
set_subpart!(G, Symbol("e2"), [7,8,5,6,6,8,5,7,9,9,9,9]); # tgtG
set_subpart!(H, Symbol("e1"), [1,1,3,3,7,7,9,9,2,4,6,8]); # srcH
set_subpart!(H, Symbol("e2"), [2,4,8,6,6,2,4,8,5,5,5,5]); # tgtH
test_iso(G,H)

modtrip = to_cset(from_cset(G, true),GraphG, true)
@test is_isomorphic(G, modtrip)

q1 = diagram_to_query(SGcone);
q2 = diagram_to_query(u_monic);
xg = graph_to_cset(SimpleGraphG)();
for i in 1:3 add_parts!(xg, Symbol("x$i"), 3) end
for i in 1:6 set_subpart!(xg, Symbol("e$i"), [3,3,3]) end
q3 = @relation (x1_1=x1_1, x1_2=x1_2) begin
    x1(_id=x1_1)
    x1(_id=x1_2)
end;
@test length(query(xg,q3))==9


# TEST DIAGRAM TO QUERY
r = diagram_to_query(id(Triangle));

rel = @relation (x1_1=x1_1,x2_2=x2_2,x3_3=x3_3) begin
 x1(_id=x1_1, e1=x2_2, e2=x3_3)
 x2(_id=x2_2, e3=x3_3)
 x3(_id=x3_3)
end;
@test is_isomorphic(r, rel)

tri = graph_to_cset(Triangle)();
for i in 1:3 add_parts!(tri, Symbol("x$i"), 2) end
for i in 1:3 set_subpart!(tri, Symbol("e$i"), [1,2]) end
res = query(tri, rel);
for i in 1:2
    @test res[i] == (x1_1=i,x2_2=i,x3_3=i)
end

# TEST PATHS TO QUERY
xgraph = Graph(4); # two paths that meet up but intersect along the way
add_edges!(xgraph, [1,2,1,2,4],[2,3,2,4,3]);
xg = graph_to_cset(xgraph)();
for i in 1:4 add_parts!(xg, Symbol("x$i"), 2); end
for (i, p) in enumerate([[1,2],[2,1],[2,1],[2,1],[2,2]])
    set_subpart!(xg, Symbol("e$i"),p);
end

p1 = [1,2]  # (12)→(12)→(21)  # pen1 = 1;2, last1 = 2;1
p2 = [3,4,5] # (12)→(21)→(12)→(22) # pen2 = 1;2, last2=2;2
q = paths_to_query(xgraph, p1, p2)
rel = @relation (start=init, pen1=p_1_1, pen2=p_2_2,
                 last1=p_1_2, last2=p_2_3) begin
 x1(_id=init, e1=p_1_1, e3=p_2_1)
 x2(_id=p_1_1, e2=p_1_2)
 x2(_id=p_2_1, e4=p_2_2)
 x4(_id=p_2_2, e5=p_2_3)
end
@test is_isomorphic(q, rel)

# Empty path test
xg = graph_to_cset(Loop)();
add_parts!(xg, Symbol("x1"), 3);
set_subpart!(xg, Symbol("e1"), [2,1,3]);
q = paths_to_query(Loop, [1],Int[]);
rel = @relation (start=init, pen1=init,pen2=init,last1=p_1_1,last2=init) begin
 x1(_id=init, e1=p_1_1)
end;
@test is_isomorphic(q, rel)

G = to_combinatorial(Model(SetPermSketch, [2]), SetPermSketch)
# can't color refine b/c it's an acset

G,H = init_graphs(SetPermSketch.G, [2])
set_subpart!(G, :e1, [2,1])
set_subpart!(G, :e2, [2,1])
set_subpart!(H, :e1, [1,1])
set_subpart!(H, :e2, [2,2])
test_iso(G,H,false)

modtrip = to_cset(from_cset(G, true),SetPermSketch.G, true)
@test is_isomorphic(modtrip, G)
end

# START
m = find_models(MonoSketch, [1,1]);

find_models(SetPermSketch, [1])

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

#mono_res = find_models(MonoSketch, Dict([2=>2])) # ID and swap, not tt or ff
#include("findmodel.jl");

catmodel = Model(CatSketch, [1,2,4,8])


find_models(MonoSketch, [2,3])



"""Remove cleanly - not needed for the FK values b/c nothing points to them"""
function remove(orig::CSet{CD},rem::Dict{Symbol, Set{Int}})::CSet where {CD}

    function reindex(n::Int, removed::Vector{Int})::Vector{Int}
        offset, off_counter, o_index = [],0,1
        for i in 1:n
        while o_index <= length(removed) && removed[o_index] < i
            if removed[o_index] < i
            off_counter +=1
            end
            o_index += 1
        end
        push!(offset, off_counter)
        end
        return offset
    end
    tabs, arrs, src, tgt = ob(CD), hom(CD), dom(CD), codom(CD)
    res = deepcopy(orig)
    offsets = Dict{Symbol, Vector{Int}}()
    saved = Dict{Symbol, Vector{Int}}()
    for (tab, reminds) in collect(rem)
        n = nparts(orig, tab)
        rem_parts!(res, tab, 1:n)
        add_parts!(res, tab, n - length(reminds))
        offsets[tab] = reindex(n, sort(collect(reminds)))
        saved[tab] = [i for i in 1:n if !(i in reminds)]
    end
    println("SAVED $saved")
    for (a, s, t) in zip(arrs, src, tgt)
        println("readjusting a $a s $s t $t tabs[s] $(tabs[s]) ")
        srcinds = get(saved, tabs[s], 1:nparts(orig,s))
        offs = get(offsets, tabs[t], zeros(Int,nparts(orig, t)))
        println("with srcinds $srcinds and offs $offs")
        new=[val - offs[val] for val in orig[a][srcinds]]
        set_subpart!(res, a, new)
    end
    return res
end

