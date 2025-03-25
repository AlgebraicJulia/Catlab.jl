module TestChase

using Test, Catlab
using Catlab.CategoricalAlgebra.Chase: egd, tgd, crel_type, pres_to_eds,
  from_c_rel, collage

# ACSetTransformations as ACSets on the collage
###############################################

h = homomorphism(path_graph(Graph, 2), path_graph(Graph, 3); initial=(V=[1,2],))
_, col = collage(h)
col[Symbol("α_V")] == h[:V] |> collect
col[Symbol("α_E")] == h[:E] |> collect


# Factorizing EDs
#----------------

# We can factor a ED that combines EGD and TGD aspects
etgd_s = path_graph(Graph, 3)
etgd_t = @acset Graph begin
  V = 2; E=3; src=[1,1,2]; tgt=[1,2,1]
end
# cset common to both tgd and egd
core = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

# This adds a self loop to #1 and merges #1/#3
etgd = ACSetTransformation(etgd_s,etgd_t; V=[1,2,1], E=[2,3])

@test is_isomorphic(codom(egd(etgd)), core) # EGD has no extra self-edge
@test collect(egd(etgd)[:V]) == [1,2,1] # but it does merge vertices

@test is_isomorphic(dom(tgd(etgd)), core) # TGD does not merge
@test codom(tgd(etgd)) == codom(etgd) # but it does add the self edge


# School example
#---------------
@present SchSchool(FreeSchema) begin
  (TA, Student, Faculty, Person)::Ob
  t_s::Hom(TA, Student)
  t_f::Hom(TA, Faculty)
  s_p::Hom(Student, Person)
  f_p::Hom(Faculty, Person)

  compose(t_s, s_p) == compose(t_f, f_p)
end
@acset_type School(SchSchool)

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
ed = ACSetTransformation(ed1, ed2; d...)
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
ed = ACSetTransformation(pg, biarr, V=[2,1], E=[2])

# Initial instance
tri = path_graph(Graph, 3)
add_edge!(tri, 3, 1)

# Expected result
sym_tri = deepcopy(tri)
add_edges!(sym_tri, [2,3,1],[1,2,3])

# terminates in one step
eds = Dict(:R=>ed)
@test is_isomorphic(sym_tri, codom(first(chase(tri, eds, 3))))
# terminates instantly
@test biarr == codom(first(chase(biarr, eds, 3)))

# Chases that require computation in C-Rel
#-----------------------------------------

@present ThLoop(FreeSchema) begin
  X::Ob
  x::Hom(X, X)
  compose(x, x, x) == compose(x, x)
end
@acset_type Loop(ThLoop)
LoopRel = crel_type(ThLoop;name="Loop")

# Constraints to encode that x is a function
unique_l,unique_r,total_l,three_two_l,three_two_r = [LoopRel() for _ in 1:5]
add_parts!(unique_l,:X,3); 
add_parts!(unique_l,:x,2;src_x=[1,1],tgt_x=[2,3]);
add_parts!(unique_r,:X,2); 
add_part!(unique_r,:x;src_x=1,tgt_x=2);
ED_unique = homomorphism(unique_l, unique_r)
add_part!(total_l,:X)
ED_total = ACSetTransformation(total_l, unique_r; X=[1])
# x-path of length 3 = x-path of length 2
add_parts!(three_two_l,:X,6); 
add_parts!(three_two_l,:x,5; src_x=[1,2,3,1,5],tgt_x=[2,3,4,5,6] ); 

add_parts!(three_two_r,:X,5); 
add_parts!(three_two_r,:x,5; src_x=[1,2,3,1,5],tgt_x=[2,3,4,5,4]); 

ED_three_two = ACSetTransformation(three_two_l, three_two_r;
                                   X=[1,2,3,4,5,4], x=[1,2,3,4,5])

loop_eds = pres_to_eds(ThLoop; name="Loop") # autogenerate from schema
@test loop_eds[:Eq1] == ED_three_two
@test force(loop_eds[:x_total]) == ED_total
@test loop_eds[:x_uni] == ED_unique

# Compute the chase
res, succ = chase(total_l, loop_eds, 5)
@test succ
@test codom(from_c_rel(res,Loop())[1]) == @acset Loop begin X=3; x=[2,3,3] end

end # module
