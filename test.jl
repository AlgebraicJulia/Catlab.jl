
include("modelfind.jl");
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra

#############################
# LEFT INVERSE / INVOLUTION #
#############################

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
srch = consts -> search(fls, consts, [:A,:B],[:id,:f,:g,:inv])
# inv can be swap or id, f is forced to be an iso
@test length(search(fls,[2,2])) == 2
# inv can be swap or id, f's choices are symmetric.
@test length(search(fls,[1,2])) == 2
# Cannot have injective function to smaller cardinality
@test length(search(fls,[2,1])) == 0

# There are 4 nonisomorphic options for A=2,B=3:
# inv can be id OR swap 2 of the three elements in B.
# There is only one automorph where inv is id, and
# if B swaps, then f(1) and f(2) can map to the swapped
# elements, in which case there is just one automorph.
# There are two automorphs in the case where only one out of
# f(1),f(2) is in the swapped pair in B. These are
# distinguished by whether or not the element of g that is
# not mapped to maps to the A whose image in in the swap or not.
@test length(search(fls,[2,3]))==4

############
# PULLBACK #
############

# Two function α⇉β and their pullback f×ᵦg
G = Graph(3);
add_edges!(G, [1,1,3,3],[2,2,1,1]); # 1=f 2=g 3=π₁ 4=π₂
cone_dia=Graph(4);
add_edges!(cone_dia, [1,3,4,4],[2,2,1,3]); # ASSUMING LAST IND IS APEX
cone_T = T(cone_dia, G, V=[1,2,1,3], E=[1,2,3,4]);
fls = FLS(G, T[], T[cone_T]);
srch = consts -> search(fls, consts,
    [:α,:β,Symbol("f×ᵦg")],[:f,:g,:π₁,:π₂])

# The pullback is empty because no f=[1,1] and g=[2,2]
@test length(search(fls,[2,2,0])) == 1

# There are 4 models.
# f=[1,2], g=[1,2] means the pullback is {(1,1),(2,2)}
# f=[1,2], g=[1,1] means the pullback is {(1,1),(1,2)}
# f=[1,1], g=[1,2] means the pullback is {(1,1),(2,1)}
# f=[2,1], g=[1,2] means the pullback is {(1,2),(2,1)}
@test length(search(fls,[2,2,2]))==4

# If f,g map to same element, then pullback is A×A
@test length(search(fls,[2,2,4]))==1

####################
# SET PERMUTATIONS #
####################

SetPermG = Graph(1);
add_edges!(SetPermG, [1,1], [1,1]); # f, g
SetPermDia = Graph(2);
add_edges!(SetPermDia, [1,2],[2,1]); # f;g = id
SetPermSketch=FLS(SetPermG, T[T(SetPermDia, SetPermG,V=[1,1],E=[1,2])], T[]);
srch = i -> search(SetPermSketch, [i], [:A], [:f,:g]);

# Isomorphism classes of permutations
# [1]=id, [2]= adds swap, [3] adds a 3-cycle,
# [4] adds a 4-cycle + having two swaps
iso_perms = [1,2,3,5]
for (i, n_perms) in enumerate(iso_perms)
    @assert length(search(SetPermSketch, [i])) == n_perms
end

####################
# REFLEXIVE GRAPHS #
####################

ReflG = Graph(2);  # V E
add_edges!(ReflG,[2,2,1,1], [1,1,1,2]); # src, tgt, id, refl
ReflGDia = Graph(2);
add_edges!(ReflGDia,[1,1,2,2],[1,2,1,1]);
RGT = T(ReflGDia, ReflG, V=[1,2], E=[3,4,1,2]);
ReflSketch = FLS(ReflG, T[RGT], T[]);
srch = cs -> search(ReflSketch, cs, [:V,:E],
                    [:src,:tgt,:id,:refl]);

# Single node with self loop
for (consts, expected) in [
    [1,1]=>1,
    [0,1]=>0,   # arrow needs a vertex
    [1,0]=>0,   # vertex needs an id arrow
    [2,2]=>1,   # both arrows must be id
    [2,3]=>2,   # the non-id arrow can bridge or not
    [2,4]=>(2+  # 2 loops (either same vertex or not),
            2+  # 1 loop (either ↺← or ↺→)
            2)] # 0 loops (either ⇆ or ⇉)
    @test length(search(ReflSketch,consts)) == expected
end

###########################
# CONSTANT (arrow from 1) #
###########################

ConG = Graph(2) # 1=1 2=A
add_edges!(ConG,[1,1],[2,2])
Con2Sketch = FLS(ConG, T[], T[T(Graph(1),ConG,V=[1])]);
srch = cs -> search(Con2Sketch, cs, [Symbol("1"),:A],
                    [:a₁,:a₂]);

# Only one option if codomain is singleton
@test length(search(Con2Sketch, [1,1])) == 1

# with two constants, they can either be the same or different
for i in 2:5
    @test length(search(Con2Sketch, [1,i])) == 2
end

# Nothing for the terminal object to map to
@test length(search(Con2Sketch, [1,0])) == 0

# Terminal object must be singleton, no more, no less
for i in 0:5
    @test length(search(Con2Sketch, [0,i])) == 0
    @test length(search(Con2Sketch, [2,i])) == 0
end

####################################
# Infinite sequence of a's and b's #
####################################

InfListG = Graph(3) # 1, d, l
add_edges!(InfListG,[1,1,3,3],[2,2,2,3])  # a, b, head, tail
Span2 = Graph(3)
add_edges!(Span2, [3,3],[1,2]);

InfListSketch=FLS(InfListG, T[],T[
  T(Graph(1), InfListG, V=[1]),
  T(Span2,InfListG;V=[2,3,3],E=[3,4])]);
srch = cs -> search(InfListSketch, cs, [Symbol("1"),:d,:l],
                    [:a,:b,:head,:tail]);

for combo in cartprod(0:3,0:3,0:3)
    n1, nd, nl = combo
    # terminal object must have 1
    # 1 must have something to send a,b to
    # no results if either of these don't happen
    if n1 != 1 || nd == 0
        expected = 0
    # |L|=|L|x|D| satisfied trivially when |L|=0
    # just have the number of ways for a,b to map to D
    elseif nl == 0 #
        expected = nd == 1 ? 1 : 2 # either to same elem or different, if |D| > 1
    elseif nd == 1
        expected = iso_perms[nl]
    else
        expected = 0 # nd > 1, and nl >0, so |L|=|L|x|D| impossible to solve
    end
    length(search(InfListSketch,collect(combo))) == expected
end

##############
# SEMIGROUPS #
##############

# Too computationally intensive to do anything nontrivial (|s| > 1)
# So wait until we can combine results from smaller theories into
# larger ones before tackling this.
SGG = Graph(3); # s s² s³
add_edges!(SGG, [2, 2, 2, 3, 3, 3,   3,   3,    3,   3],
                [1, 1, 1, 1, 1, 1,   2,   2,    2,   2]);
#                k  π₁ π₂ Π₁ Π₂ Π₃ π₁×π₂ π₂×π₃ id×k k×id
s, s², s³ = 1:3
k,π₁,π₂,Π₁,Π₂,Π₃,π₁π₂,π₂π₃,idk,kid = 1:10
s3dia = Graph(12)
add_edges!(s3dia, [1,1,1,2,2,
                   1,1,1,5,5,
                   1,2,8,8,1,
                   5,10,10,8,10],
                  [2,3,4,3,4,
                   5,6,7,6,7,
                   8,9,9,4,10,
                   11,3,11,12,12])
s3T = T(s3dia, SGG, V=[s³,s²,s,s,s²,s,s,s²,s,s²,s,s],
                    E=[π₁π₂, Π₁, Π₂, π₁, π₂,
                       π₂π₃, Π₂, Π₃, π₁, π₂,
                       kid, k,  π₁,  π₂, idk,
                       k,   π₁, π₂,  k,  k]);
Span2 = Graph(3)
add_edges!(Span2, [3,3],[1,2]);
Span3 = Graph(4);
add_edges!(Span3, [4,4,4],[1,2,3]);

SgSketch = FLS(SGG, T[s3T], T[
    T(Span2, SGG, V=[s,s,s²],  E=[π₁, π₂]),
    T(Span3, SGG, V=[s,s,s,s³],E=[Π₁,Π₂,Π₃])]);
srch = cs -> search(SgSketch, cs, [:s, :s², :s³],
                    [:k,:π₁,:π₂,:Π₁,:Π₂,:Π₃,
                     :π₁π₂,:π₂π₃,:idk,:kid]);

res = search(SgSketch, [2,4,8]; verbose=true);