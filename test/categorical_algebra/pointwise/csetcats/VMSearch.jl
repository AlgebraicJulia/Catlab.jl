module TestCSetVMSearch

using Catlab, Test

# Graph
#######

# Look for path graph
#--------------------
g = path_graph(Graph, 3)
h = erdos_renyi(Graph, 100, 0.05)

@test_throws ErrorException compile_hom_search(g, strat=:xxxxxx);
prog1 = compile_hom_search(g, strat=:neighbor)
prog2 = compile_hom_search(g, strat=:connected)

@test sprint(show, prog1) isa String

expected = length(homomorphisms(g, h))
@test all(==(expected), map([prog1,prog2]) do prog 
  length(homomorphisms(g, h; alg=VMSearch(), prog))
end)

# Random VM 
prog3 = compile_hom_search(g, strat=:random)
h = erdos_renyi(Graph, 20, 0.05) # small, b/c random can be very inefficient
@test length(homomorphisms(g,h; alg=VMSearch(), prog=prog3)) == length(homomorphisms(g,h))


# DDS 
######

@present SchDDS(FreeSchema) begin
  X::Ob
  Φ::Hom(X,X)
end
@acset_type DDS(SchDDS, index=[:Φ])

DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end # random DDS

for _ in 1:10
  g, h = DDS.([10,150])
  prog1 = compile_hom_search(g, strat=:neighbor);
  prog2 = compile_hom_search(g, strat=:connected);

  expected = length(homomorphisms(g, h))
  @test all(==(expected), map([prog1,prog2]) do prog 
    length(homomorphisms(g, h; alg=VMSearch(), prog))
  end)
end

end # module
