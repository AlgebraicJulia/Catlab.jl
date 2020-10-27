module TestScheduleUndirectedWiringDiagrams
using Test

using Catlab.WiringDiagrams, Catlab.Programs.RelationalPrograms
using Catlab.WiringDiagrams.ScheduleUndirectedWiringDiagrams:
  composites, composite_junction, composite_ports, parent, box_parent

# Closed cycle
##############

d = @relation () where (w,x,y,z) begin
  R(w,x)
  S(x,y)
  T(y,z)
  U(z,w)
end

s = sequential_schedule(d)
@test length(composites(s)) == 3
@test parent(s) == [2,3,3]
@test box_parent(s) == [1,1,2,3]

nd = to_nested_diagram(s)
@test parent(nd) == [2,3,3]
@test box_parent(nd) == [1,1,2,3]
@test map(length, composite_ports(nd, 1:3)) == [2,2,0]
@test composite_junction(nd, composite_ports(nd, 1)) == [1,3]
@test composite_junction(nd, composite_ports(nd, 2)) == [4,1]

end
