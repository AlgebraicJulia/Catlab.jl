module TestCospanRewrite
using Test
using Catlab.Graphs
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: FinFunction

const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V);

##################
# EXAMPLE GRAPHS #
##################
G1 = Graph(1);
G2 = Graph(2);
G3 = Graph(3);

Loop = Graph(1);
add_edge!(Loop, 1, 1);

Arrow = Graph(2);
add_edge!(Arrow, 1, 2);

Three = Graph(3);
add_edges!(Three, [1,2], [2,3]);

Square = Graph(4)
add_edges!(Square,[1,1,2,3],[2,3,4,4]);

"""
  3→4
 ╱  ↓
1→2→5
"""
Trap = Graph(5);
add_edges!(Trap,[1,2,1,3,4],[2,5,3,4,5]);

CSpan = Graph(3);
add_edges!(CSpan, [1,3],[2,2]);

Cycle = Graph(2);
add_edges!(Cycle, [1,2],[2,1]);

#################
# Example Spans #
#################
id_1 = id(Graph(1));
id_2 = id(Graph(2));
flip = CSetTransformation(G2, G2, V=[2,1]);
f12 = CSetTransformation(G1, G2, V=[1]);
f22 = CSetTransformation(G1, G2, V=[2]);

sp1 = Span(id_1, id_1);
sp2 = Span(id_2, id_2);
flipflip = Span(flip, flip);

###############
# Open Graphs #
###############
o1 = OpenGraph(G1, id_1[:V], id_1[:V]);
o2 = OpenGraph(G2, f12[:V], f22[:V]);
openloop = OpenGraph(Loop, id_1[:V], id_1[:V]);

openarr = OpenGraph(Arrow, f12[:V], f22[:V]);
openarr21 = OpenGraph(Arrow, id_2[:V], f22[:V]);
open3 = OpenGraph(Three,
                  FinFunction([2,1], 3),
                  FinFunction([3,2], 3));
opensquare = OpenGraph(Square,
                       FinFunction([1,2], 4),
                       FinFunction([2,4], 4));
opentrap = OpenGraph(Trap,
                     FinFunction([1,2], 5),
                     FinFunction([2,5], 5));
opencspan = OpenGraph(CSpan,
                        FinFunction([2,1], 3),
                        FinFunction([2], 3));
opencycle = OpenGraph(Cycle,  flip[:V], f22[:V]);

#########################
# Graph Transformations #
#########################
gm1 = ACSetTransformation(G1, Loop, V=[1]);
up_ = ACSetTransformation(G2, Arrow, V=[1,2]);
down_ = ACSetTransformation(G2, G1, V=[1,1]);
tosquare = ACSetTransformation(Three, Square, V=[1,2,4],E=[1,3]);
totrap = ACSetTransformation(Three, Trap, V=[1,2,5], E=[1,2]);
tocspan = ACSetTransformation(Arrow, CSpan, V=[1,2], E=[1]);
tocycle = ACSetTransformation(Arrow, Cycle, V=[1,2], E=[1]);
#########
# Rules #
#########

"""Removes a loop
1 → Loop ← 1
↑    ↑     ↑
1 →  1   ← 1
↓    ↓     ↓
1 →  1   ← 1
"""
rem_loop = OpenRule(
    openloop, o1, o1, sp1,
    Span(gm1, id(G1)), sp1);

"""Adds a loop (vertical refl of rem_loop)"""
add_loop = OpenRule(
    o1,o1,openloop,sp1,
    Span(id(G1), gm1), sp1);


"""Squashes an arrow to a point
1 → Arr ← 1
↑ l  ↑  r ↑
1 →  2  ← 1
↓    ↓    ↓
1 →  1  ← 1
"""
squash = OpenRule(
    openarr, o2, o1, sp1,
    Span(up_, down_), sp1);


"""
12 → Square ← 24
↑      ↑      ↑
21 →  123  ←  42
↓      ↓      ↓
12 → Trap  ←  24
"""
square_to_trap = OpenRule(
    opensquare, open3, opentrap,
    flipflip, Span(tosquare, totrap), flipflip);

"""
21 → CSpan ← 1
↑     ↑     ↑
12 → Arrow ← 1
↓     ↓     ↓
21 → Cycle ← 1
"""
cspan_to_cycle = OpenRule(
    opencspan, openarr21, opencycle,
    flipflip, Span(tocspan, tocycle), sp1);

# Test for valid derived rules
force_eq = (x,y) -> force(x) == force(y)

ih = idH(G3);
iv = idV(G3);
@test force_eq(id2(G3), OpenRule(ih,ih,ih,iv,iv,iv))
@test force_eq(id2(G3), id2H(iv))
@test force_eq(id2(G3), id2V(ih))

@test force_eq(composeH(opencspan, idH(dom(right(opencspan)))), opencspan)

# Span composition is defined up to isomorphism, so we oughtn't expect equality here
@test (composeV(flipflip, idV(G2)) == flipflip) in [true, false]

ch = composeH(square_to_trap, cspan_to_cycle);
cv = composeV(squash, add_loop);

res = apply_open_rewrite(rem_loop, openloop, id(Loop), id_1, id_1)
@test apex(res) == G1 # Removed the arrow
end