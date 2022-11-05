module TestSchemas 

using Test
using Catlab.Schemas

bsch = BasicSchema([:E,:V], [(:src,:E,:V),(:tgt,:E,:V)],[:Weight],[(:weight,:E,:Weight)])
tsch = typelevel(bsch)
for sch in [bsch, tsch]
  @test collect(ob(sch)) == collect(objects(sch)) == [:E,:V]
  @test collect(attrtype(sch)) ==  collect(attrtypes(sch)) == [:Weight]
  @test hom(sch) == homs(sch; just_names=true) == [:src, :tgt]
  @test isempty(homs(sch; from=:V))
  @test homs(sch; from=:E) == homs(sch)
  @test attr(sch) == attrs(sch; just_names=true) == [:weight]
  @test arrows(sch) == homs(sch) ∪ attrs(sch)
  @test dom(sch, :src) == :E
  @test dom(sch, :weight) == :E
  @test dom_nums(sch) == (1,1)
  @test codom_nums(sch) == (2,2)
  @test adom_nums(sch) == (1,)
  @test acodom_nums(sch) == (1,)
end

@test attrtype_instantiation(tsch, Tuple{Int}, :Weight) == Int

end # module
