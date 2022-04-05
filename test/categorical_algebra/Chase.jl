module TestChase
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra.Chase
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph
import Catlab.CategoricalAlgebra.FinCats: is_natural


is_natural(D::DiagramHom) =
  is_functorial(shape_map(D)) && is_natural((diagram_map(D)))

# Factorizing EDs
#----------------
gED = ED{Graph, ACSetTransformation}

# We can factor a ED that combines EGD and TGD aspects
etgd_s = path_graph(Graph, 3)
etgd_t = @acset Graph begin
  V = 2; E=3; src=[1,1,2]; tgt=[1,2,1]
end
# cset common to both tgd and egd
core = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

# This adds a self loop to #1 and merges #1/#3
etgd = gED(ACSetTransformation(etgd_s,etgd_t; V=[1,2,1], E=[2,3]))

@test is_isomorphic(codom(egd(etgd)), core) # EGD has no extra self-edge
@test collect(egd(etgd)[:V]) == [1,2,1] # but it does merge vertices

@test is_isomorphic(dom(tgd(etgd)), core) # TGD does not merge
@test codom(tgd(etgd)) == codom(etgd.ST) # but it does add the self edge


# School example
#---------------
@present ThSchool′(FreeSchema) begin
  (TA′, Student′, Faculty′)::Ob
  t_s′::Hom(TA′, Student′)
  t_f′::Hom(TA′, Faculty′)
end

@present ThSchool(FreeSchema) begin
  (TA, Student, Faculty, Person)::Ob
  t_s::Hom(TA, Student)
  t_f::Hom(TA, Faculty)
  s_p::Hom(Student, Person)
  f_p::Hom(Faculty, Person)

  compose(t_s, s_p) == compose(t_f, f_p)
end
@acset_type School(ThSchool)
@acset_type School′(ThSchool′)

# Construct ED to enforce the path equality
ed1 = @acset School begin
    TA = 1; Student = 1; Faculty = 1; Person = 2
    t_s = [1]; t_f = [1]; s_p = [1]; f_p = [2]
end
ed2 = @acset School begin
  TA = 1 ;Student = 1 ;Faculty = 1 ;Person = 1
  t_s = [1] ;t_f = [1] ;s_p = [1] ;f_p = [1]
end
d = Dict([:TA=>[1], :Student=>[1], :Faculty=>[1], :Person=>[1,1]])
sED = ED{School, ACSetTransformation}
ed = sED(ACSetTransformation(ed1, ed2; d...))
# initializing db from an instance with 5 faculty, 4 students, and 2 TAs
# when we freely add elements due to functionality, we get 9 elements in Person
unchased = @acset School begin
    TA = 2; Student = 4; Faculty = 5; Person = 9
    t_s = [1,2]; t_f = [1,2]; s_p = [1,2,3,4]; f_p = [5,6,7,8,9]
end
# Because the first two Faculty are the same people as the first two students
# We expect the result to have only 7 people and for f_p[1:2] == s_p[1:2]
expected = @acset School begin
    TA = 2; Student = 4; Faculty = 5; Person = 7
    t_s = [1,2]; t_f = [1,2]; s_p = [1,2,3,4]; f_p = [1,2,5,6,7]
end

chaseres, _ = chase(unchased, Dict(:R=>ed), 1)
@test is_isomorphic(expected, codom(chaseres))

# Symmetric digraph example
#--------------------------

# Construct ED that symmetrizes arrows
pg = path_graph(Graph, 2)  # 1 --> 2
biarr = deepcopy(pg)       # 1 <-> 2
add_edge!(biarr, 2, 1)
ed = gED(ACSetTransformation(pg, biarr, V=[2,1], E=[2]))

# Initial instance
tri = path_graph(Graph, 3)
add_edge!(tri, 3, 1)

# Expected result
sym_tri = deepcopy(tri)
add_edges!(sym_tri, [2,3,1],[1,2,3])

# terminates in one step
@test is_isomorphic(sym_tri, codom(first(chase(tri, Dict(:R=>ed), 3))))
# terminates instantly
@test biarr == codom(first(chase(biarr, Dict(:R=>ed), 3)))

# Chases that require computation in C-Rel
#-----------------------------------------

@present ThLoop(FreeSchema) begin
  X::Ob
  x::Hom(X, X)
  compose(x, x, x) == compose(x, x)
end
@acset_type Loop(ThLoop)
LoopRel = crel_type(ThLoop, :Loop)
lED = ED{LoopRel, ACSetTransformation}

# Constraints to encode that x is a function
unique_l = @acset LoopRel begin  X=3; x=2; src_x=[1,1]; tgt_x=[2,3] end
unique_r = @acset LoopRel begin  X=2; x=1; src_x=[1]; tgt_x=[2] end
ED_unique = homomorphism(unique_l, unique_r)
total_l = @acset LoopRel begin X=1 end
ED_total = homomorphism(total_l, unique_r)
# x-path of length 3 = x-path of length 2
three_two_l = @acset LoopRel begin
  X=6; x=5; src_x=[1,2,3,1,5]; tgt_x=[2,3,4,5,6] end
three_two_r = @acset LoopRel begin
  X=5; x=5; src_x=[1,2,3,1,5]; tgt_x=[2,3,4,5,4] end
ED_three_two = ACSetTransformation(three_two_l, three_two_r;
                                   X=[1,2,3,4,5,4], x=[1,2,3,4,5])
ΣX = lED.([ED_unique,ED_total,ED_three_two])

loop_eds = pres_to_eds(ThLoop, :Loop) # autogenerate from schema
@test loop_eds[:Eq1].ST == ED_three_two
@test loop_eds[:x_total].ST == ED_total
@test loop_eds[:x_uni].ST == ED_unique

# Compute the chase
res, succ = chase_crel(total_l, loop_eds, 5; I_is_crel=true, Σ_is_crel=true,
                      cset_example=Loop(), verbose=false)
@test succ
@test codom(res) == @acset Loop begin X=3; x=[2,3,3] end


# Left Kan of diagram in Set
############################

SchoolC, SchoolC′ = FinCat.([ThSchool, ThSchool′])
F = FinFunctor(Dict(:TA′=>:TA, :Faculty′=>:Faculty, :Student′=>:Student),
               Dict(:t_s′=>:t_s,:t_f′=>:t_f), SchoolC′, SchoolC)

I = @acset School′ begin
  TA′=2; Student′=4; Faculty′=5
  t_s′=[1,2]; t_f′=[1,2]
end

lk, chase_res = leftkan(F, I, :School)
@test is_natural(lk)

@test is_isomorphic(expected, School(diagram(codom(lk))))

# Left kan of Diagrams in Grph
##############################

const Grph = ACSetCat{Graph}

# Set up example shape categories
#-------------------------------

@present ThArr(FreeSchema) begin
  (A,B)::Ob; f::Hom(A,B)
end
@present ThArr2(FreeSchema) begin
  (C,D)::Ob; m::Hom(C,D); n::Hom(D, C); compose(m,n) == id(C)
end
@present ThInv(FreeSchema) begin
  (Y)::Ob; f::Hom(Y,Y); compose(f,f) == id(Y)
end
@present ThOne(FreeSchema) begin
  (X)::Ob
end

@present ThInv2(FreeSchema) begin
  (Y)::Ob; f::Hom(Y,Y); compose(f,f) == f
end

pres_to_eds(ThInv2, :Inv2) # example of an equation with a :generator term


Arr, Arr2, One, Inv = FinCat.([ThArr, ThArr2, ThOne, ThInv])

# Set up graph data
#-------------------
two = path_graph(Graph, 2)
ar = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
h1, h2 = homomorphisms(two, ar)

# Freely adding a right inverse to a C-set transformation: f: A->B
#-----------------------------------------------------------------
F = FinFunctor(Dict(:A=>:C, :B=>:D), Dict(:f=>:m), Arr, Arr2)
# This may require adding things to A. These must then be mapped to B in a
# distinct place, thereby adding to B, too.
I = FinDomFunctor(Dict(:A=>two,:B=>ar),Dict(:f=>h1),Arr,Grph())
lk = diagram(codom(leftkan(F, I, :X; verbose=false)))
# This homomorphism is injective on vertices. Those can be easily inverted.
# However, V2 in the codomain has a self loop not present in V2 of the domain.
# Therefore the domain has an extra loop added to it.
@test ob_map(lk, :C) == ar
# The new edge ISN'T forced to match to the self loop in the codomain, though
@test ob_map(lk, :D) == @acset Graph begin V=2; E=3; src=[1,2,2]; tgt=2 end

# This homomorphism sends V1 and V2 to V2 of the codomain.
I = FinDomFunctor(Dict(:A=>two,:B=>ar),Dict(:f=>h2),Arr,Grph())
lk2 = diagram(codom(leftkan(F, I, :X2; verbose=false)))
@test is_isomorphic(ob_map(lk2, :C), ar)
# TODO: rationalize why this is the result, if it's correct
@test ob_map(lk2, :D) == @acset Graph begin V=3; E=3; src=[1,3,2]; tgt=3 end

# Freely adding an involution
#----------------------------
F = FinFunctor(Dict(:X=>:Y),nothing,One,Inv)
# creates a copy of the starting graph, and the involution is a swap function.
I = FinDomFunctor(Dict(:X=>two), nothing, One, Grph())
lk3 = diagram(codom(leftkan(F, I, :XF; verbose=false)))
@test ob_map(lk3, :Y) == two ⊕ two
@test collect(hom_map(lk3, :f)[:V]) == [3,4,1,2]
@test collect(hom_map(lk3, :f)[:E]) == [2,1]

end # module