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
  input::Ob
  transitions::Ob
  output::Ob

  is::Hom(input,species)
  it::Hom(input,transitions)
  os::Hom(output,species)
  ot::Hom(output,transitions)
end

PetSet = CSetType(SITOS, index=[:is,:it,:os,:ot])

# macro petset(head, body)
#     name = @match head begin
#         name::Symbol => name
#         _ => throw(ParseError("Ill-formed petset header $head"))
#     end
#     let_expr = Expr(:let, Expr(:block), translate_petset(body))
#     esc(Expr(:(=), name, let_expr))
# end

# function translate_petset(body::Expr)::Expr
#     @assert body.head == :block
#     code = Expr(:block)
#     append_expr!(code, :(_petset = PetSet()))
#     for expr in strip_lines(body).args
#         append_expr!(code, translate_expr(expr))
#     end
#     append_expr!(code, :(_petset))
#     code
# end

# function translate_expr(expr::Expr)::Expr
#     @match expr begin
#         Expr(:(::), [name::Symbol, type::Symbol]) =>
#             :(add_part!(_petset, $(QuoteNode(type)), []))
#         Expr(:(::), [name::Symbol, Expr(:call, [type::Symbol, args...])])
#         _ => throw(ParseError("Ill-formed petset declaration $expr"))
#     end
# end

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
                add_parts!(ps,:input,ins[s],(is=j,it=i))
            end
            if s in keys(outs)
                add_parts!(ps,:output,outs[s],(os=j,ot=i))
            end
        end
    end
    return ps
end

graph_attrs = Attributes(:rankdir=>"LR")
node_attrs  = Attributes(:shape=>"plain", :style=>"filled", :color=>"white")
edge_attrs  = Attributes(:splines=>"splines")

function Graph(ps)
    snodes = [Node(string("S_$s"), Attributes(:shape=>"circle", :color=>"#6C9AC3")) for s in 1:nparts(ps,:species)]
    tnodes = [Node(string("T_$k"), Attributes(:shape=>"square", :color=>"#E28F41")) for s in 1:nparts(ps,:transitions)]

    iedges = map(1:nparts(ps,:input)) do i
        s = subpart(ps,k,:is)
        t = subpart(ps,k,:it)
        Edge(["S_$s","T_$t"],Attributes())
    end
    oedges = map(1:nparts(ps,:output)) do i
        s = subpart(ps,k,:os)
        t = subpart(ps,k,:ot)
        Edge(["T_$t","S_$s"],Attributes())
    end

    stmts = vcat(snodes,tnodes,iedges,oedges)
    Graphviz.Graph("G",true,stmts,graph_attrs,node_attrs,edge_attrs)
end
