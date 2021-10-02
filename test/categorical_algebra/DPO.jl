module TestDPO
using Test
using Catlab.Graphs
using Catlab.Present
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra.FinSets
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra

# Wiring diagrams
#################

A, B, C, D = [:A], [:B], [:C], [:D];
f,g,h,i = Box(:f, A, B), Box(:g, B, C),Box(:h, C, D), Box(:i, [:D,:B], [:D,:B]);

GWD = WiringDiagram([:A,:A],[:D,:B])
fv, gv, hv, fv2 = add_box!(GWD, f), add_box!(GWD, g), add_box!(GWD, h), add_box!(GWD, f);
add_wires!(GWD, Pair[
  (input_id(GWD),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(GWD),1),
  (input_id(GWD),2) => (fv2,1),
  (fv2,1) => (output_id(GWD),2)]);

RWD = WiringDiagram([], []);
fv, iv, gv = add_box!(RWD, Box(:f,[],B)), add_box!(RWD, i), add_box!(RWD, Box(:g,B,[]));
add_wires!(RWD, Pair[(iv,1) => (iv, 1),
                     (fv, 1) => (iv, 2),
                     (iv, 2)=>(gv,1)]);

LWD = WiringDiagram([], []);
fv, gv = add_box!(LWD, Box(:f,[],B)), add_box!(LWD, Box(:g,B,[]));
add_wires!(LWD, Pair[
  (fv,1) => (gv,1),
]);


IWD = WiringDiagram([], []);
fv, gv = add_box!(IWD, Box(:f,[],[])), add_box!(IWD, Box(:g,[],[]));

XWD = WiringDiagram([:A,:A],[:D,:B])
fv, gv, hv = add_box!(XWD, f), add_box!(XWD, g), add_box!(XWD, h)
fv2, iv = add_box!(XWD, f), add_box!(XWD, i);
add_wires!(XWD, Pair[
  (input_id(XWD),1) => (fv,1),
  (iv,1) => (iv, 1), (fv, 1) => (iv, 2), (iv, 2)=>(gv,1),
  (gv,1) => (hv,1),
  (hv,1) => (output_id(XWD),1),
  (input_id(XWD),2) => (fv2,1),
  (fv2,1) => (output_id(XWD),2)]);

L=ACSetTransformation(IWD.diagram, LWD.diagram, Box=[1,2]);
R=ACSetTransformation(IWD.diagram, RWD.diagram, Box=[1,3]);
m=ACSetTransformation(LWD.diagram, GWD.diagram, Box=[1,2],InPort=[2],OutPort=[1],Wire=[1]);
@test is_isomorphic(XWD.diagram, rewrite_match(L,R,m))

# Graphs with attributes
########################

@present TheoryDecGraph(FreeSchema) begin
  E::Ob
  V::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)

  X::AttrType
  dec::Attr(E,X)
end

@present TheoryLabelledDecGraph <: TheoryDecGraph begin
  label::Attr(V,X)
end

@acset_type LabelledDecGraph(TheoryLabelledDecGraph, index=[:src,:tgt])

aI2 = @acset LabelledDecGraph{String} begin
  V = 2
  E = 0
  label = ["a","b"]
end

aarr = @acset LabelledDecGraph{String} begin
  V = 2
  E = 1
  src = [1]
  tgt = [2]
  dec = ["e1"]
  label = ["a","b"]
end

abiarr = @acset LabelledDecGraph{String} begin
  V = 2
  E = 2
  src = [1,2]
  tgt = [2,1]
  dec = ["e1","rev_e1"]
  label = ["a","b"]
end

aspan = @acset LabelledDecGraph{String} begin
  V = 3
  E = 2
  src = [1,1]
  tgt = [2,3]
  dec = ["e1","e2"]
  label = ["a","b","c"]
end

expected = @acset LabelledDecGraph{String} begin
  V = 3
  E = 3
  src = [1,1,2]
  tgt = [2,3,1]
  dec = ["e1","e2","rev_e1"]
  label = ["a","b","c"]
end


L = ACSetTransformation(aI2, aarr, V=[1,2]);
R = ACSetTransformation(aI2, abiarr, V=[1,2]);
m = ACSetTransformation(aarr, aspan, V=[2,1], E=[1]);  # sends 'a'->'b' and 'b'->'a'

@test_throws ErrorException("ACSet colimit does not exist: label attributes a != b") rewrite_match(L,R,m)

m = ACSetTransformation(aarr, aspan, V=[1,2], E=[1]);

@test is_isomorphic(expected, rewrite_match(L, R, m))

# Graphs
########

# Example graphs
I2 = Graph(2)
I3 = Graph(3)
#   e1   e2
# 1 <- 2 -> 3
span = Graph(3)
add_edges!(span, [2,2],[1,3])
# 1 -> 2
arr = path_graph(Graph, 2)
# 1 <-> 2
biarr = Graph(2)
add_edges!(biarr, [1,2],[2,1])
# 1 -> 2 -> 3 -> 1
tri = cycle_graph(Graph, 3)
# 4 <- 1 -> 2 and 2 <- 3 -> 4
dispan = Graph(4)
add_edges!(dispan, [1,1,3,3],[2,4,2,4])

#      e1
#    1 -> 2
# e2 |  / ^
#    vv   | e4
#    4 -> 3
#      e5
squarediag = Graph(4)
add_edges!(squarediag, [1,1,2,3,4],[2,4,4,2,3])

# Add a reverse arrow to span
span_w_arrow = Graph(3)
add_edges!(span_w_arrow,[1,1,2],[2,3,1])

L = CSetTransformation(I2, arr, V=[1,2])
R = CSetTransformation(I2, biarr, V=[1,2])
m = CSetTransformation(arr, span, V=[2,1], E=[1])
@test is_isomorphic(span_w_arrow, rewrite_match(L, R, m))

# Remove apex of a subspan (top left corner of squarediag, leaves the triangle behind)
L = CSetTransformation(I2, span, V=[1,3])
m = CSetTransformation(span, squarediag, V=[2,1,4], E=[1,2])
@test is_isomorphic(tri, rewrite_match(L,id(I2),m))

# Remove self-edge using a *non-monic* match morphism
two_loops = Graph(2)
add_edges!(two_loops,[1,2],[1,2]) # ↻1   2↺
one_loop = Graph(2)
add_edges!(one_loop,[2],[2]) # 1   2↺

L = CSetTransformation(I2, arr, V=[1,2])
m = CSetTransformation(arr, two_loops, V=[1, 1], E=[1])
@test is_isomorphic(one_loop, rewrite_match(L,id(I2),m))

# Simplest non-trivial, non-monic exmaple
@present TheoryFinSet(FreeSchema) begin
  X::Ob
end
@acset_type FinSetType(TheoryFinSet)

I, L, G = [FinSetType() for _ in 1:3]
add_parts!(I,:X,2)
add_parts!(L,:X,1)
add_parts!(G,:X,1)
l = CSetTransformation(I,L,X=[1,1])
m = CSetTransformation(L,G,X=[1])
@test can_pushout_complement(l,m)
ik, kg = pushout_complement(l,m)
# There are 3 functions `ik` that make this a valid P.C.
# codom=1 with [1,1], codom=2 with [1,2] or [2,1]
K = codom(ik)
@test nparts(K, :X) == 1 # algorithm currently picks the first option

# Non-discrete interface graph. Non-monic matching
arr_loop= Graph(2)
add_edges!(arr_loop,[1,2],[2,2])  # 1->2↺
arrarr = Graph(2)
add_edges!(arrarr, [1,1],[2,2]) #  1⇉2
arrarr_loop = Graph(2)
add_edges!(arrarr_loop,[1,1,2],[2,2,2]) # 1⇉2↺
arr_looploop = Graph(2)
add_edges!(arr_looploop, [1,2,2],[2,2,2]) # 1-> ↻2↺

L = CSetTransformation(arr, arr, V=[1,2],E=[1]) # identity
R = CSetTransformation(arr, arrarr, V=[1,2], E=[1])
m = CSetTransformation(arr, arr_loop, V=[2,2], E=[2]) # NOT MONIC
@test is_isomorphic(arr_looploop, rewrite_match(L,R,m))

# only one monic match
@test is_isomorphic(arrarr_loop, rewrite(L, R, arr_loop, monic=true))

# two possible morphisms L -> squarediag, but both violate dangling condition
L = CSetTransformation(arr, span, V=[1,2], E=[1]);
m = CSetTransformation(span, squarediag, V=[2,1,4], E=[1,2]);
@test (:src, 5, 4) in dangling_condition(ComposablePair(L,m))

# violate id condition because two orphans map to same point
L = CSetTransformation(I2, biarr, V=[1,2]); # delete both arrows
m = CSetTransformation(biarr, arr_loop, V=[2,2], E=[2,2]);
@test (1, 2) in id_condition(ComposablePair(L[:E],m[:E]))[2]
L = CSetTransformation(arr, biarr, V=[1,2], E=[1]); # delete one arrow
@test 1 in id_condition(ComposablePair(L[:E],m[:E]))[1]

span_triangle = Graph(3); # 2 <- 1 -> 3 (with edge 2->3)
add_edges!(span_triangle,[1,1,2], [2,3,3]);

L = CSetTransformation(arr, tri, V=[1,2], E=[1]);
m = CSetTransformation(tri, squarediag, V=[2,4,3], E=[3,5,4]);
@test is_isomorphic(span_triangle, rewrite_match(L,id(arr),m))

k, g = pushout_complement(L, m); # get PO complement to do further tests

# the graph interface is equal to the final graph b/c we only delete things
@test is_isomorphic(span_triangle, codom(k))

# Check pushout properties 1: apex is the original graph
@test is_isomorphic(squarediag, ob(pushout(L, k))) # recover original graph

# Check pushout properties 2: the diagram commutes
Lm = compose(L,m);
kg = compose(k,g);
for I_node in 1:2
  @test Lm[:V](I_node) == kg[:V](I_node)
end
@test Lm[:E](1) == kg[:E](1)

# Check pushout properties 3: for every pair of unmatched things between K and L, they are NOT equal
for K_node in 1:3
  @test m[:V](3) != g[:V](K_node)
end

for K_edge in 2:3
  @test m[:E](3) != g[:E](K_edge)
end

# Undirected bipartite graphs
#############################

# 1 --- 1
#    /
# 2 --- 2

z_ = UndirectedBipartiteGraph()
add_vertices₁!(z_, 2)
add_vertices₂!(z_, 2)
add_edges!(z_, [1,2,2], [1,1,2])

line = UndirectedBipartiteGraph()
add_vertices₁!(line, 1)
add_vertices₂!(line, 2)
add_edges!(line, [1], [1])

parallel = UndirectedBipartiteGraph()
add_vertices₁!(parallel, 2)
add_vertices₂!(parallel, 2)
add_edges!(parallel, [1,2], [1,2])

merge = UndirectedBipartiteGraph()
add_vertices₁!(merge, 2)
add_vertices₂!(merge, 2)
add_edges!(merge, [1,2], [1,1])

Lspan = UndirectedBipartiteGraph()
add_vertices₁!(Lspan, 1)
add_vertices₂!(Lspan, 2)
add_edges!(Lspan, [1,1],[1,2])

I = UndirectedBipartiteGraph()
add_vertices₁!(I, 1)
add_vertices₂!(I, 2)

L = CSetTransformation(I, Lspan, V₁=[1], V₂=[1,2])
R = CSetTransformation(I, line, V₁=[1], V₂=[1,2])
m1 = CSetTransformation(Lspan, z_, V₁=[1], V₂=[1,2], E=[1, 2])
m2 = CSetTransformation(Lspan, z_, V₁=[1], V₂=[2,1], E=[2, 1])

@test is_isomorphic(parallel, rewrite_match(L, R, m1))
@test is_isomorphic(merge, rewrite_match(L, R, m2))

# Structured cospan rewriting
#############################

# Horizontal composition of epidemiological model rewrites
#---------------------------------------------------------

@present TheoryPetriNet(FreeSchema) begin
  (T,S,I,O)::Ob
  it::Hom(I,T)
  is::Hom(I,S)
  ot::Hom(O,T)
  os::Hom(O,S)
end

@acset_type PetriNet(TheoryPetriNet);

const OpenPetriNetOb, OpenPetriNet = OpenCSetTypes(PetriNet,:S);
ns = x->nparts(x,:S)
Open(p::PetriNet) = OpenPetriNet(p, map(x->FinFunction([x], ns(p)), 1:ns(p))...);
Open(p::PetriNet, legs...) = OpenPetriNet(p, map(l->FinFunction(l, ns(p)), legs)...);
Open(n, p::PetriNet, m) = Open(p, n, m);
o1, o2 = OpenPetriNetOb(1), OpenPetriNetOb(2);
L = typeof(o1).parameters[1]
v1, v2 = idV_(o1), idV_(o2);
i1, i2, i3 = (id(FinSet(x)) for x in 1:3)
idH_(o1); # test if it fails

isquare = id2_(o1);
composeV_(isquare, isquare)

iv2 = id2H_(Span(i1,i1), o1);

SIR = @acset PetriNet begin # S ->[si]⇉← I → R
    S = 3 # S I R
    T = 2 # si ir
    I = 3
    O = 3
    it = [1,2,1]
    ot = [1,2,1]
    is = [1,2,2]
    os = [2,3,2]
end;
oSIR = Open([1], SIR, [2,3]);
ioSIR = id2V_(oSIR);

SEIR = @acset PetriNet begin # S ->[si]⇉← I → R
    S = 4 # S I R E
    T = 3 # si ir ei
    I = 4
    O = 4
    it = [1,2,1,3]
    ot = [1,2,1,3]
    is = [1,2,2,4]
    os = [2,3,4,2]
end;
oSEIR = Open([1], SEIR, [2,3]);
# SIR minus one of the infection arrows to I
# which will instead be going to E
sirOverlap = @acset PetriNet begin
    S = 3 # S I R
    T = 2 # si ir
    I = 3
    O = 2
    it = [1,2,1]
    ot = [1,2]
    is = [1,2,2]
    os = [2,3]
end;
osirOverlap = Open([1], sirOverlap, [2,3]);
sirUp = ACSetTransformation(sirOverlap, SIR,
    S=[1,2,3],T=[1,2],I=[1,2,3],O=[1,2]);
sirDown = ACSetTransformation(sirOverlap, SEIR,
    S=[1,2,3],T=[1,2],I=[1,2,3],O=[1,2]);

expose_up = StructuredMultiCospanHom(osirOverlap, oSIR, [sirUp, L(i1), L(i2)]);
expose_down = StructuredMultiCospanHom(osirOverlap, oSEIR,
                                       [sirDown, L(i1), L(i2)]);
expose = openrule(Span(expose_up, expose_down));


IQR = @acset PetriNet begin # I -> Q -> R
    S = 3 # I Q R
    T = 2 # iq qr
    I = 2
    O = 2
    it = [1, 2]
    ot = [1, 2]
    is = [1, 2]
    os = [2, 3]
end;
oIQR = Open([1,3],IQR, [2]);

IQRescape = @acset PetriNet begin # I ↔ Q -> R
    S = 3 # I Q R
    T = 3 # iq qr qi
    I = 3
    O = 3
    it = [1, 2, 3]
    ot = [1, 2, 3]
    is = [1, 2, 2]
    os = [2, 3, 1]
end;
oIQRescape = Open([1,3],IQRescape, [2]);

IQRinj = ACSetTransformation(IQR, IQRescape,
    S=[1,2,3], T=[1,2], I=[1,2], O=[1,2]);

escape_up = left(id2V_(oIQR).data)
escape_down = StructuredMultiCospanHom(oIQR, oIQRescape, ACSetTransformation[IQRinj, right(v2), right(v1)])
escape = openrule(Span(escape_up, escape_down))

# WRITE REWRITE RULES FOR THESE TWO COMPONENTS INDIVIDUALLY
# CAN COMBINE INTO A LARGER REWRITE RULE
expose_escape = composeH_(expose, escape); # exposes S and Q
bottom = apex(right(expose_escape.data).tgt)
expected_bottom = @acset PetriNet begin
    S = 5 # S I R E Q
    T = 6
    O = 7
    I = 7
         # si ir ei iq qr qi
    it = [1,1,2, 3, 4, 5, 6]
    ot = [1,1,2, 3, 4, 5, 6]
    is = [1,2,2, 4, 2, 5, 5]
    os = [2,4,3, 2, 5, 3, 2]
end
@test is_isomorphic(bottom, expected_bottom)

# Program optimization example
#-----------------------------
# Rewrite ⦿→□→⦿→□→⦿ into ⦿→□→⦿
# Dangling condition prevents us from applying this where compression is invalid
o_interface = Open([1], L(FinSet(2)), [2])
a_pattern = @acset PetriNet begin
  S = 3
  T = 2
  I = 2
  O = 2
  is = [1,2]
  it = [1,2]
  ot = [1,2]
  os = [2,3]
end
a_result = @acset PetriNet begin
  S = 2
  T = 1
  I = 1
  O = 1
  is = [1]
  it = [1]
  ot = [1]
  os = [2]
end
o_pattern = Open([1], a_pattern, [3])
o_result = Open([1], a_result, [2])
o_up = ACSetTransformation(L(FinSet(2)), a_pattern, S=[1,3])
o_down =ACSetTransformation(L(FinSet(2)), a_result, S=[1,2])
L_morph = StructuredMultiCospanHom(o_interface, o_pattern, [o_up, L(i1), L(i1)])
c_rule = openrule(Span(L_morph,
  StructuredMultiCospanHom(o_interface, o_result, [o_down, L(i1), L(i1)])))

#  1 a 2 b 3 c 4 d 5
#  ⦿→□→⦿→□→⦿→□→⦿→□→⦿
#   ↘           ↘
#6 ⦿←□  e     f □→⦿ 7
# The first branch does NOT impede rewriting top row
# But the second branch does
prog = @acset PetriNet begin
  S = 7
  T = 6
  I = 6
  O = 6
  is = [1,2,3,4,1,4]
  it = [1,2,3,4,5,6]
  ot = [1,2,3,4,5,6]
  os = [2,3,4,5,6,7]
end
o_prog = Open([1],prog,[3])

# After applying two rewrites, the result should be
#  1 a 2 b 3
#  ⦿→□→⦿→□→⦿
#   ↘   ↘
#4 ⦿←□   □→⦿ 5

expected2 = @acset PetriNet begin
  S = 5
  T = 4
  I = 4
  O = 4
  is = [1,2,1,2]
  it = [1,2,3,4]
  ot = [1,2,3,4]
  os = [2,3,4,5]
end

# However, we can only apply one rewrite unless we change the new interface
#  1 a 2 b 3 c 4
#  ⦿→□→⦿□→⦿→□→⦿
#   ↘      ↘
#5 ⦿←□ d  e □→⦿ 6

expected2 = @acset PetriNet begin
  S = 6
  T = 5
  I = 5
  O = 5
  is = [1,2,3,1,3]
  it = [1,2,3,4,5]
  ot = [1,2,3,4,5]
  os = [2,3,4,5,6]
end


@test length(open_homomorphisms(o_pattern, o_prog)) == 1
m = open_homomorphisms(o_pattern, o_prog)[1].maps[1];
l = left(c_rule.data).maps[1];
@test is_isomorphic(apex(open_rewrite(c_rule, o_prog)), expected2)

end #module
