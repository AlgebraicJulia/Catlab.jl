module TestScheduleUndirectedWiringDiagrams
using Test

using Catlab.WiringDiagrams, Catlab.Programs.RelationalPrograms
using Catlab.WiringDiagrams.ScheduleUndirectedWiringDiagrams:
  composites, parent, box_parent

# Sequential schedule
#####################

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

end
