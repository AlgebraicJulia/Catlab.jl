module TestChase

using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra.Chase
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra

# School example from Fast Left Kan Extensions paper
#---------------------------------------------------
@present ThSchool(FreeSchema) begin
  (TA, Student, Faculty, Person)::Ob
  t_s::Hom(TA, Student)
  t_f::Hom(TA, Faculty)
  s_p::Hom(Student, Person)
  f_p::Hom(Faculty, Person)

  compose(t_s, s_p) == compose(t_f, f_p)
end
@acset_type School(ThSchool)

# Construct ED to enforce the path equality
ed1 = @acset School begin
    TA = 1
    Student = 1
    Faculty = 1
    Person = 2
    t_s = [1]
    t_f = [1]
    s_p = [1]
    f_p = [2]
end
ed2 = @acset School begin
    TA = 1
    Student = 1
    Faculty = 1
    Person = 1
    t_s = [1]
    t_f = [1]
    s_p = [1]
    f_p = [1]
end
d = Dict([:TA=>[1], :Student=>[1], :Faculty=>[1], :Person=>[1,1]])
ed = ED(ACSetTransformation(ed1, ed2; d...))
# initializing db from an instance with 5 faculty, 4 students, and 2 TAs
# when we freely add elements due to functionality, we get 9 elements in Person
unchased = @acset School begin
    TA = 2
    Student = 4
    Faculty = 5
    Person = 9
    t_s = [1,2]
    t_f = [1,2]
    s_p = [1,2,3,4]
    f_p = [5,6,7,8,9]
end
# Because the first two Faculty are the same people as the first two students
# We expect the result to have only 7 people and for f_p[1:2] == s_p[1:2]
expected = @acset School begin
    TA = 2
    Student = 4
    Faculty = 5
    Person = 7
    t_s = [1,2]
    t_f = [1,2]
    s_p = [1,2,3,4]
    f_p = [1,2,5,6,7]
end

@test is_isomorphic(expected, chase(unchased, [ed], 1)[1])

# Symmetric digraph example
#--------------------------

# Construct ED that symmetrizes arrows

pg = path_graph(Graph, 2)  # 1 --> 2
biarr = deepcopy(pg)       # 1 <-> 2
add_edge!(biarr, 2, 1)
ed = ED(ACSetTransformation(pg, biarr, V=[2,1], E=[2]))

# Initial instance
tri = path_graph(Graph, 3)
add_edge!(tri, 3, 1)

# Expected result
sym_tri = deepcopy(tri)
add_edges!(sym_tri, [2,3,1],[1,2,3])

# Tests
@test is_isomorphic(sym_tri, chase(tri, [ed], 3)[1]) # terminates in one step
@test biarr == chase(biarr, [ed], 3)[1]  # terminates instantly

end