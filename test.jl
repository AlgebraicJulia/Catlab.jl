using Base: method_argnames

include("modelfind.jl");
using Test
using Catlab.Graphs
using Catlab.CategoricalAlgebra

G = @acset LabeledGraph begin
    V = 3
    E = 5
    vlabel = [:A,:B,:C]
    elabel = [:f,:h,:g, :ida, :inv]
    src = [1,1,2,1,3]
    tgt = [2,3,3,1,3]
end;

f = FLSinit(G);
tridia = @acset LabeledGraph begin
    V=3
    E = 3
    vlabel=[:A,:B,:C]
    elabel=[:f,:g,:h]
    src=[1,2,1]
    tgt=[2,3,3]
end;
add_diagram!(f, tridia);
iddia = @acset LabeledGraph begin
    V = 1
    E = 1
    vlabel = [:A]
    elabel = [:ida]
    src=  [1]
    tgt = [1]
end;
add_diagram!(f, iddia);

invdia = @acset LabeledGraph begin
    V = 2
    E = 2
    vlabel=[:C,:C]
    elabel=[:inv,:inv]
    src=[1,2]
    tgt=[2,1]
end;
add_diagram!(f, invdia);

d = get_diagram(f, :A);
Tf = TheoryFLSketch;
met = catpres_to_linear(Tf);

ct = fls_csettype(f);
# Violates ID constraint
ex_cset = @acset ct begin
    A=2
    B=1
    C=1
    ida=[2,1]
    f=[1,1]
    g=[1]
    h=[1,1]
    inv=[1]
end;

@test length(check_diagram(f, ex_cset, :C)) == 1
@test length(check_diagram(f, ex_cset, :A)) == 0
@test_throws AssertionError("Equations for A not satisfied by indices [1, 2]"
                           ) check_diagrams(f, ex_cset)

