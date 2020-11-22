module CPortGraphs
using ...Theories
using ...CategoricalAlgebra
import ...CategoricalAlgebra.CSets: migrate!
using ...Present
using ...Graphs
using ...Graphs.BasicGraphs
import ...Graphs.BasicGraphs: TheoryGraph
import ..DirectedWiringDiagrams: ocompose

export ThCPortGraph, ThOpenCPortGraph, ThSymCPortGraph, ThOpenSymCPortGraph,
  CPortGraph, OpenCPortGraph, SymCPortGraph, OpenSymCPortGraph


@present ThCPortGraph(FreeSchema) begin
    B::Ob
    P::Ob
    W::Ob

    src::Hom(W,P)
    tgt::Hom(W,P)
    box::Hom(P,B)
end

@present ThOpenCPortGraph <: ThCPortGraph begin
    OP::Ob
    con::Hom(OP, P)
end

@present ThSymCPortGraph <: ThCPortGraph begin
    inv::Hom(W, W)

    compose(inv,inv) == id(W)
    compose(inv,src) == tgt
    compose(inv,tgt) == src
end

@present ThOpenSymCPortGraph <: ThSymCPortGraph begin
    OP::Ob

    con::Hom(OP, P)
end

const CPortGraph = ACSetType(ThCPortGraph)
const OpenCPortGraph = ACSetType(ThOpenCPortGraph)
const SymCPortGraph = ACSetType(ThSymCPortGraph)
const OpenSymCPortGraph = ACSetType(ThOpenSymCPortGraph)
const OSCPGraph = OpenSymCPortGraph

function OpenCPortGraph(g::CPortGraph)
    x = OpenCPortGraph()
    copy_parts!(x, g, W=parts(g, :W), P=parts(g, :P), B=parts(g, :B))
    return x
end

function migrate!(g::Graph, cpg::CPortGraph) 
    migrate!(g, cpg,
    Dict(:E=>:W, :V=>:B),
    Dict(
        :src=>compose(ThCPortGraph[:src], ThCPortGraph[:box]),
        :tgt=>compose(ThCPortGraph[:tgt], ThCPortGraph[:box])))
end

function migrate!(pg::CPortGraph, opg::OpenCPortGraph)
    migrate!(pg, opg,
        Dict(:B=>:B, :P=>:P, :W=>:W),
        Dict(:src=>:src, :tgt=>:tgt, :box=>:box)
    )
end

function migrate!(pg::CPortGraph, g::Graph)
    migrate!(pg, g,
      Dict(:B=>:V, :P=>:V, :W=>:E),
      Dict(
        #   :src=>ThCPortGraph[:src]⋅ThCPortGraph[:box],
        #   :tgt=>ThCPortGraph[:tgt]⋅ThCPortGraph[:box],
          :box=>id(TheoryGraph[:V]),
          :src=>TheoryGraph[:src],
          :tgt=>TheoryGraph[:tgt],
      )
    )
end

function migrate!(og::OpenCPortGraph, g::CPortGraph)
    migrate!(og, g, 
        Dict(:B=>:B, :P=>:P, :W=>:W, :OP=>:P),
        Dict(
            :src=>:src,
            :tgt=>:tgt,
            :box=>:box,
            :con=>id(ThCPortGraph[:P])
        ))
end
migrate!(og::OpenCPortGraph, g::Graph) = migrate!(og, migrate!(CPortGraph(),g))

function migrate!(pg::SymCPortGraph, g::SymmetricGraph)
    migrate!(pg, g,
      Dict(:B=>:V, :P=>:V, :W=>:E),
      Dict(
          :box=>id(TheorySymmetricGraph[:V]),
          :src=>id(TheorySymmetricGraph[:src]),
          :tgt=>id(TheorySymmetricGraph[:tgt]),
          :inv=>TheorySymmetricGraph[:inv],
      )
    )
end

function ocompose(g::OpenCPortGraph, xs::Vector)
    u = coproduct(xs)
    sum = apex(u)
    for e in parts(g, :W)
        s = subpart(g, e, :src)
        t = subpart(g, e, :tgt)
        sbox = subpart(g, s, :box)
        tbox = subpart(g, t, :box)
        incident(g, sbox, :box)
        localport_src = findfirst(s .== incident(g, sbox, :box))
        localport_tgt = findfirst(t .== incident(g, tbox, :box))
        ι_srcport = legs(u.cocone)[sbox][:P](localport_src)
        ι_tgtport = legs(u.cocone)[tbox][:P](localport_tgt)
        add_part!(sum, :W; src=ι_srcport, tgt=ι_tgtport) 
    end
    return sum
end

end