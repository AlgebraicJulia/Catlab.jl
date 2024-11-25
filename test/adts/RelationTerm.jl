""" Relation Term Tests

The following module checks that the RelationTerm ADT successfully constructs
ACSet representation. 
"""
module RelationTermTests

using Test
using Catlab.ADTs.RelationTerm
using Catlab.WiringDiagrams.UndirectedWiringDiagrams
using Catlab.WiringDiagrams.RelationDiagrams
using Catlab.Programs.RelationalPrograms
using ACSets.ACSetInterface

@testset "UWD Show" begin
  # Untyped Case
  # parsed = @relation (x,z) where (x,y,z) begin
  # R(x,y)
  # S(y,z)
  # end

  v1 = Untyped(:x)
  v2 = Untyped(:y)
  v3 = Untyped(:z)
  c = [v1, v2, v3]
  op = [v1, v3]
  s = [Statement(:R, [v1, v2]), Statement(:S, [v2, v3])]
  u = UWDExpr(op, c, s) 

  @test sprint(show, u) ==
   "{ R(x, y)\n  S(y, z) } where {x, y, z}"

  # Typed Case
  # parsed = @relation (x,y,z) where (x::X, y::Y, z::Z, w::W) begin
  # R(x,w)
  # S(y,w)
  # T(z,w)
  # end

  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  v4 = Typed(:w, :W)
  c = [v1, v2, v3, v4]
  op = [v1, v2, v3]
  s = [Statement(:R, [v1, v4]), Statement(:S, [v2, v4]), Statement(:T, [v3, v4])]
  u = UWDExpr(op, c, s)

  @test sprint(show, u) ==
  "{ R(x:X, w:W)\n  S(y:Y, w:W)\n  T(z:Z, w:W) } where {x:X, y:Y, z:Z, w:W}"

  # Named Port Case
  # parsed = @relation (start=u, stop=w) where (u, v, w) begin
  # E(src=u, tgt=v)
  # E(src=v, tgt=w)
  # end
  v1 = Untyped(:u)
  v2 = Untyped(:v)
  v3 = Untyped(:w)
  c = [v1, v2, v3]
  op = [Kwarg(:start, v1), Kwarg(:stop, v3)]
  s = [Statement(:E, [Kwarg(:src, v1), Kwarg(:tgt, v2)]), Statement(:E, [Kwarg(:src, v2), Kwarg(:tgt, v3)])]
  u = UWDExpr(op, c, s)

  @test sprint(show, u) ==
  "{ E(src=u, tgt=v)\n  E(src=v, tgt=w) } where {u, v, w}"

end

@testset "UWD Construction" begin
  # Untyped Case
  # parsed = @relation (x,z) where (x,y,z) begin
  # R(x,y)
  # S(y,z)
  # end

  v1 = Untyped(:x)
  v2 = Untyped(:y)
  v3 = Untyped(:z)
  c = [v1, v2, v3]
  op = [v1, v3]
  s = [Statement(:R, [v1, v2]), Statement(:S, [v2, v3])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)
  
  d = RelationDiagram(2)
  add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
  add_junctions!(d, 3, variable=[:x,:y,:z])
  set_junction!(d, [1,2,2,3]) #Understanding: Port 1 connects to 1, port 2 to 2, port 3 to 2, port 4 to 3
  set_junction!(d, [1,3], outer=true)

  @test uwd_result == d

  # Typed Case
  # parsed = @relation (x,y,z) where (x::X, y::Y, z::Z, w::W) begin
  # R(x,w)
  # S(y,w)
  # T(z,w)
  # end

  v1 = Typed(:x, :X)
  v2 = Typed(:y, :Y)
  v3 = Typed(:z, :Z)
  v4 = Typed(:w, :W)
  c = [v1, v2, v3, v4]
  op = [v1, v2, v3]
  s = [Statement(:R, [v1, v4]), Statement(:S, [v2, v4]), Statement(:T, [v3, v4])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)

  d = RelationDiagram([:X,:Y,:Z])
  add_box!(d, [:X,:W], name=:R)
  add_box!(d, [:Y,:W], name=:S)
  add_box!(d, [:Z,:W], name=:T)
  add_junctions!(d, [:X,:Y,:Z,:W], variable=[:x,:y,:z,:w])
  set_junction!(d, [1,4,2,4,3,4])
  set_junction!(d, [1,2,3], outer=true)
  @test uwd_result == d

  # Named Port Case
  # parsed = @relation (start=u, stop=w) where (u, v, w) begin
  # E(src=u, tgt=v)
  # E(src=v, tgt=w)
  # end

  v1 = Untyped(:u)
  v2 = Untyped(:v)
  v3 = Untyped(:w)
  c = [v1, v2, v3]
  op = [Kwarg(:start, v1), Kwarg(:stop, v3)]
  s = [Statement(:E, [Kwarg(:src, v1), Kwarg(:tgt, v2)]), Statement(:E, [Kwarg(:src, v2), Kwarg(:tgt, v3)])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)

  d = RelationDiagram(2, port_names=[:start, :stop])
  add_box!(d, 2, name=:E)
  add_box!(d, 2, name=:E)
  add_junctions!(d, 3, variable=[:u,:v,:w])
  set_junction!(d, [1,2,2,3])
  set_junction!(d, [1,3], outer=true)
  set_subpart!(d, :port_name, [:src, :tgt, :src, :tgt])
  @test uwd_result == d

  # Inferred Context case
  # parse = @relation (x,z) -> (R(x,y); S(y,z))

  v1 = Untyped(:x)
  v2 = Untyped(:y)
  v3 = Untyped(:z)
  c = []
  op = [v1, v3]
  s = [Statement(:R, [v1, v2]), Statement(:S, [v2, v3])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)

  d = RelationDiagram(2)
  add_box!(d, 2, name=:R); add_box!(d, 2, name=:S)
  add_junctions!(d, 3, variable=[:x,:z,:y])
  set_junction!(d, [1,3,3,2]) #Understanding: Port 1 connects to 1, port 2 to 2, port 3 to 2, port 4 to 3
  set_junction!(d, [1,2], outer=true)
  
  @test uwd_result == d

  # Infered Outer Ports with named ports
  # parse = @relation ((;) where (v,)) -> E(src=v, tgt=v)
  v1 = Untyped(:v)
  c = [v1]
  op = []
  s = [Statement(:E, [Kwarg(:src, v1), Kwarg(:tgt, v1)])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)
  @test subpart(uwd_result, :port_name) == [:src, :tgt]

  # Inferred Outer Ports with no names
  #   sird_uwd = @relation () where (S::Pop, I::Pop, R::Pop, D::Pop) begin
  #   infect(S,I,I,I) # inf
  #   disease(I,R) # recover
  #   disease(I,D) # die
  #   end
  v1 = Typed(:S, :Pop)
  v2 = Typed(:I, :Pop)
  v3 = Typed(:R, :Pop)
  v4 = Typed(:D, :Pop)
  c = [v1, v2, v3, v4]
  op = []
  s = [Statement(:infect, [v1, v2, v2, v2]), Statement(:disease, [v2, v3]), Statement(:disease, [v2, v4])]
  u = UWDExpr(op, c, s)

  uwd_result = RelationTerm.construct(RelationDiagram, u)
  @test all(==(:Pop), subpart(uwd_result, :port_type))

end

end