using Match
using Catlab.Meta, Catlab.Syntax
using Catlab.Graphics.Graphviz
import Catlab.Graphics.Graphviz: Graph, Edge
using Petri
using LabelledArrays

using Catlab
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets

@present SITOS(FreeCategory) begin
  species::Ob
  inputs::Ob
  transitions::Ob
  outputs::Ob

  is::Hom(inputs,species)
  it::Hom(inputs,transitions)
  os::Hom(outputs,species)
  ot::Hom(outputs,transitions)
end

PetSet = CSetType(SITOS, index=[:is,:it,:os,:ot])

nspecies(ps::PetSet) = nparts(ps,:species)
ntransitions(ps::PetSet) = nparts(ps,:transitions)
ninputs(ps::PetSet) = nparts(ps,:inputs)
noutputs(ps::PetSet) = nparts(ps,:outputs)

# Need a better name for this
function from_std_petri(S,T)
    n = length(S)
    ps = PetSet()
    add_parts!(ps,:species,n)
    ks = keys(T)
    m = length(ks)
    add_parts!(ps,:transitions,m)
    for i in 1:m
        ins = T[ks[i]][1]
        outs = T[ks[i]][2]
        for j in 1:n
            s = S[j]
            if s in keys(ins)
                add_parts!(ps,:inputs,ins[s],(is=j,it=i))
            end
            if s in keys(outs)
                add_parts!(ps,:outputs,outs[s],(os=j,ot=i))
            end
        end
    end
    ps
end

function transition_matrix(ps)
    T = zeros(Int64,(ntransitions(ps),nspecies(ps),2))
    for i in 1:ninputs(ps)
        T[subpart(ps,i,:it),subpart(ps,i,:is),1] += 1
    end
    for i in 1:noutputs(ps)
        T[subpart(ps,i,:ot),subpart(ps,i,:os),2] += 1
    end
    T
end

graph_attrs = Attributes(:rankdir=>"LR")
node_attrs  = Attributes(:shape=>"plain", :style=>"filled", :color=>"white")
edge_attrs  = Attributes(:splines=>"splines")

function Graph(ps)
    snodes = [Node(string("S_$s"), Attributes(:shape=>"circle", :color=>"#6C9AC3")) for s in 1:nparts(ps,:species)]
    tnodes = [Node(string("T_$t"), Attributes(:shape=>"square", :color=>"#E28F41")) for t in 1:nparts(ps,:transitions)]

    iedges = map(1:ninputs(ps)) do i
        s = subpart(ps,i,:is)
        t = subpart(ps,i,:it)
        Edge(["S_$s","T_$t"],Attributes())
    end
    oedges = map(1:noutputs(ps)) do o
        s = subpart(ps,o,:os)
        t = subpart(ps,o,:ot)
        Edge(["T_$t","S_$s"],Attributes())
    end

    stmts = vcat(snodes,tnodes,iedges,oedges)
    Graphviz.Graph("G",true,stmts,graph_attrs,node_attrs,edge_attrs)
end

function rate_eq(ps)
    n = ntransitions(ps)
    m = nspecies(ps)
    rates = zeros(m)
    T = transition_matrix(ps)
    function f(du,u,p,t)
        for i in 1:n
            rates[i] = p[i] * prod(u[j] ^ T[i,j,1] for j in 1:m)
        end
        for j in 1:m
            du[j] = sum(rates[i] * (T[i,j,2]-T[i,j,1]) for i in 1:n)
        end
    end
    f
end
