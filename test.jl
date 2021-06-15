using Base: method_argnames

include("modelfind.jl");
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: ReflexiveGraph, TheoryReflexiveGraph


######################################################################
met = catpres_to_linear(TheoryReflexiveGraph);
r1, r2 = ReflexiveGraph(2), ReflexiveGraph(2)
set_subpart!(r2,:src,[1,1])
@test length(check_diagram(met, r1, :V)) == 2
@test length(check_diagram(met, r2, :V)) == 1

@test check_diagrams(met, r1)
@test_throws AssertionError("Equations for V not satisfied by indices [2]"
                           ) check_diagrams(met, r2)

###########################################################################

#########################
# COMMUTATIVE TRIANGLE  #
#########################

f = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 5
    vlabel = [:A,:B,:C]
    elabel = [:f,:h,:g, :ida, :inv]
    src    = [1,  1, 2,  1,    3]
    tgt    = [2,  3, 3,  1,    3]
end)

# f;g = h
add_diagram!(f, @acset LabeledGraph begin
    V = 3
    E = 3
    vlabel = [:A,:B,:C]
    elabel = [:f,:g,:h]
    src    = [1, 2, 1]
    tgt    = [2, 3, 3]
end)

# "ida" is an identity arrow
add_diagram!(f, @acset LabeledGraph begin
    V = 1
    E = 1
    vlabel = [:A]
    elabel = [:ida]
    src = [1]
    tgt = [1]
end);

# "inv" is an involution on C
add_diagram!(f, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:C, :C]
    elabel = [:inv, :inv]
    src = [1, 2]
    tgt = [2, 1]
end)

######################################################################

#############################
# LEFT INVERSE / INVOLUTION #
#############################

leftinv = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:A,:B]
    elabel = [:f,:g, :ida, :inv]
    src    = [1,  2,  1,   2]
    tgt    = [2,  1,  1,   2]
end);

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:A, :B]
    elabel = [:f, :g]
    src = [1, 2]
    tgt = [2, 1]
end);

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 1
    E = 1
    vlabel = [:A]
    elabel = [:ida]
    src = [1]
    tgt = [1]
end)

add_diagram!(leftinv, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:B, :B]
    elabel = [:inv, :inv]
    src = [1, 2]
    tgt = [2, 1]
end)

srch_leftinv = c->[catelems_to_cset(leftinv, r) for r in search(leftinv, c)]

for (x, y) in [[2,2]=>2, # inv can be swap or id, f is forced to be an iso
               [2,1]=>0, # injective function to smaller card
               [1,2]=>2, # inv can be swap or id, f's choices are symmetric.
               [2,3]=>4] # see below
    @test length(search(leftinv, x)) == y
end

# There are 4 nonisomorphic options for A=2,B=3:
# inv can be id OR swap 2 of the three elements in B.
# There is only one automorph where inv is id, and
# if B swaps, then f(1) and f(2) can map to the swapped
# elements, in which case there is just one automorph.
# There are two automorphs in the case where only one out of
# f(1),f(2) is in the swapped pair in B. These are
# distinguished by whether or not the element of g that is
# not mapped to maps to the A whose image in in the swap or not.

######################################################

#############
# EQUALIZER #
#############

fxb = Symbol("f×ᵦg")

equalizer = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [:A,:B,fxb]
    elabel = [:f,:g, :π1, :π2]
    src = [1,1,3,3]
    tgt = [2,2,1,1]
end)

add_cone!(equalizer, @acset LabeledGraph begin
    V = 4
    E = 4
    vlabel = [:A,:B,:A,fxb]
    elabel = [:f,:g, :π1, :π2]
    src = [1,3,4,4]
    tgt = [2,2,1,3]
end)

srch_equalizer = c->[catelems_to_cset(equalizer, r) for r in search(equalizer, c)]

# The pullback is empty because f=[1,1] and g=[2,2]
@test length(search(equalizer,[2,2,0])) == 1

# There are 4 models.
# f=[1,2], g=[1,2] means the pullback is {(1,1),(2,2)}
# f=[1,2], g=[1,1] means the pullback is {(1,1),(1,2)}
# f=[1,1], g=[1,2] means the pullback is {(1,1),(2,1)}
# f=[2,1], g=[1,2] means the pullback is {(1,2),(2,1)}
@test length(search(equalizer,[2,2,2]))==4

# If f,g map to same element, then pullback is A×A
@test length(search(equalizer,[2,2,4]))==1

######################################################
#################################
# SET PERMUTATIONS / PARTITIONS #
#################################

perm = FLSinit(@acset LabeledGraph begin
    V = 1
    E = 2
    vlabel = [:X]
    elabel = [:f, :f⁻¹]
    src = [1,1]
    tgt = [1,1]
end );

add_diagram!(perm, @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:X, :X]
    elabel = [:f, :f⁻¹]
    src = [1, 2]
    tgt = [2, 1]
end)

srch_perm = c -> [catelems_to_cset(perm, r) for r in search(perm, [c])]

# Isomorphism classes of permutations AKA PARTITIONS
# [1]=id, [2]= adds swap, [3] adds a 3-cycle,
# [4] adds a 4-cycle + having two swaps
iso_perms = [1,2,3,5]
for (i, n_perms) in enumerate(iso_perms)
    @assert length(search(perm, [i])) == n_perms
end

######################################################

####################
# REFLEXIVE GRAPHS #
####################

reflg = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:V, :E]
    elabel = [:id, :refl, :src, :tgt]
    src = [1,1,2,2]
    tgt = [1,2,1,1]
end );

add_diagram!(reflg, @acset LabeledGraph begin
    V = 2
    E = 4
    vlabel = [:V, :E]
    elabel = [:id, :refl, :src, :tgt]
    src = [1,1,2,2]
    tgt = [1,2,1,1]
end)


srch_reflg = cs -> [catelems_to_cset(reflg, r) for r in search(reflg, cs)]

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
    @test length(search(reflg,consts)) == expected
end

######################################################

###########################
# CONSTANT (arrow from 1) #
###########################
s1 = Symbol("1")
const2 = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [s1, :A]
    elabel = [:f, :g]
    src = [1,1]
    tgt = [2,2]
end);

add_cone!(const2, @acset LabeledGraph begin
    V = 1
    vlabel=[s1]
end)

srch_const2 = cs -> [catelems_to_cset(const2, r) for r in search(const2, cs)]

# Only one option if codomain is singleton
@test length(search(const2, [1,1])) == 1

# with two constants, they can either be the same or different
for i in 2:5
    @test length(search(const2, [1,i])) == 2
end

# Nothing for the terminal object to map to
@test length(search(const2, [1,0])) == 0

# Terminal object must be singleton, no more, no less
for i in 0:5
    @test length(search(const2, [0,i])) == 0
    @test length(search(const2, [2,i])) == 0
end

########################################################################

####################################
# Infinite sequence of a's and b's #
####################################

inflist = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 4
    vlabel = [s1, :d, :l]
    elabel = [:a,:b,:head,:tail]
    src = [1,1,3,3]
    tgt = [2,2,2,3]
end )

add_cone!(inflist, @acset LabeledGraph begin
    V = 1
    vlabel = [s1]
end)

add_cone!(inflist, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:d, :l, :l]
    elabel = [:head, :tail]
    src = [3,3]
    tgt = [1,2]
end)

srch_inflist = cs -> [catelems_to_cset(inflist, r) for r in search(inflist, cs)]
srch_inflist([1,0,0])

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
    length(search(inflist,collect(combo))) == expected
end

####################################################################################
#####################
# Cartesian Product #
#####################

pairs = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 2
    vlabel = [:s, :s2]
    elabel = [:p1, :p2]
    src = [2,2]
    tgt = [1,1]
end ); # s s²

add_cone!(pairs, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:s, :s, :s2]
    elabel = [:p1, :p2]
    src = [3,3]
    tgt = [1,2]
end )

srch_pairs = cs -> [catelems_to_cset(pairs, r) for r in search(pairs, cs)]


trips = FLSinit(@acset LabeledGraph begin
    V = 2
    E = 3
    vlabel = [:s, :s3]
    elabel = [:p1, :p2, :p3]
    src = [2,2,2]
    tgt = [1,1,1]
end ); # s s²

add_cone!(trips, @acset LabeledGraph begin
    V = 4
    E = 3
    vlabel = [:s, :s, :s, :s3]
    elabel = [:p1, :p2, :p3]
    src = [4,4,4]
    tgt = [1,2,3]
end )

srch_trips = cs -> [catelems_to_cset(trips, r) for r in search(trips, cs)]


######################################################################

##############
# SEMIGROUPS #
##############

p1p2, p2p3, idk, kid = Symbol("π₁×π₂"), Symbol("π₂×π₃"), Symbol("id×k"), Symbol("k×id")
semig = FLSinit(@acset LabeledGraph begin
    V = 3
    E = 10
    vlabel = [:s, :s2, :s3]
    elabel = [:k, :π₁, :π₂, :Π₁, :Π₂, :Π₃, p1p2, p2p3, idk, kid]
    src    = [2,  2,   2,   3,    3,   3,   3,   3,    3,   3]
    tgt    = [1,  1,   1,   1,    1,   1,   2,   2,    2,   2]
end );

# Associativity
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 4
    vlabel = [:s3, :s2, :s2, :s]
    elabel = [kid, idk, :k, :k]
    src = [1,1,2,3]
    tgt = [2,3,4,4]
end)

# Define p1p2
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 5
    vlabel = [:s3, :s, :s, :s2]
    elabel = [:Π₁, :Π₂, p1p2, :π₁, :π₂]
    src = [1,1,1,4,4]
    tgt = [2,3,4,2,3]
end)

# Define p2p3
add_diagram!(semig, @acset LabeledGraph begin
    V = 4
    E = 5
    vlabel = [:s3, :s, :s, :s2]
    elabel = [:Π₂, :Π₃, p2p3, :π₁, :π₂]
    src    = [1,    1,   1,   4,   4]
    tgt    = [2,    3,   4,   2,   3]
end)

# Define kid
add_diagram!(semig, @acset LabeledGraph begin
    V = 5
    E = 6
    vlabel = [:s3, :s2,  :s2, :s, :s]

    elabel = [p1p2, kid, :Π₃, :π₂, :k, :π₁]
    src    = [1,    1,    1,   3,   2,  3]
    tgt    = [2,    3,    4,   4,   5,  5]
end)


# Define idk
add_diagram!(semig, @acset LabeledGraph begin
    V = 5
    E = 6
    vlabel = [:s3, :s2,  :s2, :s, :s]

    elabel = [p2p3, idk, :Π₁, :π₁, :k, :π₂]
    src    = [1,    1,    1,   3,   2,  3]
    tgt    = [2,    3,    4,   4,   5,  5]
end)

# s2 is pair
add_cone!(semig, @acset LabeledGraph begin
    V = 3
    E = 2
    vlabel = [:s, :s, :s2]
    elabel = [:π₁, :π₂]
    src = [3,3]
    tgt = [1,2]
end )

# s3 is triple
add_cone!(semig, @acset LabeledGraph begin
    V = 4
    E = 3
    vlabel = [:s, :s, :s, :s3]
    elabel = [:Π₁, :Π₂, :Π₃]
    src = [4,4,4]
    tgt = [1,2,3]
end )

srch_sg = cs -> [catelems_to_cset(semig, r) for r in search(semig, cs)]

# too big to solve [2,4,8].