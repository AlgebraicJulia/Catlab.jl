include("automorphisms.jl")

G = Graph(4)
add_edges!(G,[1,2,4,4,3],[2,4,3,3,2])
direct_canon(G)

include("sketchgat.jl")
include("findmodel.jl")

#------------------------------------------------
# Tests
#------------------------------------------------


#sg_res = term_models(SimpleGraphSketch, (2,2,2))# n, a, n×n

if 1+1==1 # don't run these automatically
    q1 = diagram_to_query(nn_prod[1])
    q2 = diagram_to_query(u_monic[1])
    xg = graph_to_cset(SimpleGraphG)()
    for i in 1:3 add_parts!(xg, Symbol("x$i"), 3) end
    for i in 1:6 set_subpart!(xg, Symbol("e$i"), [3,3,3]) end
    q3 = @relation (x1_1=x1_1, x1_2=x1_2) begin
        x1(_id=x1_1)
        x1(_id=x1_2)
    end

    # indexing schema: e1::x2 → x1
    q32 = @relation (x1=x1_1,x2=x2_1) begin
    x1(_id=x1_1)
    x2(_id=x2_1) # need e1 or it fails
    end

G1, G2= graph_to_cset(Loop)(), graph_to_cset(Loop)()
add_parts!(G1,:x1,3)
add_parts!(G2,:x1,3)
set_subpart!(G1,:e1,[1,3,2])
set_subpart!(G2,:e1,[3,2,1])

cyclel, cycler = Graph(3), Graph(3)
add_edges!(cyclel,[1,2,3],[2,3,1])
add_edges!(cycler,[3,2,1],[2,1,3])
#cycs = autos(cyclel)
#bool_perms = term_models(SetPermSketch,(2,)) # finds id and swap
# mono_res = term_models(MonoSketch, (2,2)) # finds the two isomorphic swap functions


# TEST DIAGRAM TO QUERY

rg = @relation (V1=v1,V2=v2) begin
 E(src=v1, tgt=v2)
 V(_id=v1)
end

r = diagram_to_query(id(Triangle))

rel = @relation (x1_1=x1_1,x2_2=x2_2,x3_3=x3_3) begin
 x1(_id=x1_1, e1=x2_2, e2=x3_3)
 x2(_id=x2_2, e3=x3_3)
 x3(_id=x3_3)
end

@assert is_isomorphic(r, rel)

tri = graph_to_cset(Triangle)()
for i in 1:3 add_parts!(tri, Symbol("x$i"), 2) end
for i in 1:3 set_subpart!(tri, Symbol("e$i"), [1,2]) end
res = query(tri, rel)
for i in 1:2
    @assert res[i] == (x1_1=i,x2_2=i,x3_3=i)
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
@assert is_isomorphic(q, rel)

# Empty path test
xg = graph_to_cset(Loop)()
add_parts!(xg, Symbol("x1"), 3)
set_subpart!(xg, Symbol("e1"), [2,1,3])
q = paths_to_query(Loop, [1],Int[])
rel = @relation (pen1=init,pen2=init,last1=p_1_1,last2=init) begin
 x1(_id=init, e1=p_1_1)




#ms = find_models(SetPermSketch, [1]);
#mod = Model(SetPermSketch.G, [2])

CS = graph_to_cset(SetPermSketch.G)()
add_parts!(CS, :x1, 4)
set_subpart!(CS, :e1, [3,4,1,2])
set_subpart!(CS, :e2, [3,4,1,2])
canonical_iso(CS)

end


end # end of tests