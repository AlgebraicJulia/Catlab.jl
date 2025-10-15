module TestYonedaVarACSet 

using Catlab, Test

struct MyStruct 
  field::Symbol 
end
MX = MyStruct(:X)

y_Graph = yoneda(WeightedGraph{MyStruct});

# ACSet colim
#############

v3e2 = @acset_colim y_Graph begin
  v1::V; (e1,e2)::E; w::Weight
  src(e1) == v1
  tgt(e1) == src(e2)
  weight(e1)==weight(e2)
  weight(e2)== $(MyStruct(:X))
end

v3e2′ = @acset WeightedGraph{MyStruct} begin
  V=3; E=2; Weight=1; src=[1,2]; tgt=[2,3]; weight=[MX, MX] 
end

@test is_isomorphic(v3e2, v3e2′)

end # module
