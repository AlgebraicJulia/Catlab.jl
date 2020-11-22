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
    rem_parts!(sum, :OP, parts(xsum, :OP))
    for op in parts(g, :OP)
        i = g[op, [:con, :box]]
        localport = findfirst(op .== incident(g, i, :box))
        newop = legs(u.cocone)[i][:P](localport)
        add_parts!(sum, :OP, 1, con=newop)
    end
    return sum
end

@present ThBundledCPG <: ThOpenCPortGraph begin
    Bundle::Ob
    bun::Hom(OP, Bundle)
end

const BundledCPG = ACSetType(ThBundledCPG)

migrate!(b::BundledCPG, g::OpenCPortGraph) = migrate!(b,g,
    Dict(:B=>:B, :P=>:P, :W=>:W, :OP=>:OP, :Bundle=>:OP),
    Dict(:src=>:src, :tgt=>:tgt, :box=>:box,
         :con=>:con, :bun=>id(ThOpenCPortGraph[:OP]))
)

function BundledCPG(g::OpenCPortGraph)
    bg = BundledCPG()
    copy_parts!(bg, g, 
      W=parts(g,:W), P = parts(g,:P), B=parts(g, :B), OP=parts(g,:OP))
    return bg
end

function oapply(g::BundledCPG, xs::Vector)
    u = coproduct(xs)
    xsum=apex(u)
    for e in parts(g, :W)
        s = g[e,:src]
        t = g[e,:tgt]
        sbox = g[s, :box]
        tbox = g[t, :box]

        localport_src = findfirst(s .== incident(g, sbox, :box))
        localport_tgt = findfirst(t .== incident(g, tbox, :box))
        @assert length(findall(s .== incident(g, sbox, :box))) == 1
        @assert length(findall(t .== incident(g, tbox, :box))) == 1

        # println("$s:$sbox→$t:$tbox")
        sbun = incident(xs[sbox], localport_src, :bun)
        # println("sbun: $sbun")
        tbun = incident(xs[tbox], localport_tgt, :bun)
        # println("tbun: $tbun")
        for thread in zip(sbun, tbun)
            ι_srcport = legs(u.cocone)[sbox][:P](xs[sbox][thread[1], :con])
            ι_tgtport = legs(u.cocone)[tbox][:P](xs[tbox][thread[2], :con])
            # println("adding:\t $ι_srcport, $ι_tgtport")
            add_part!(xsum, :W; src=ι_srcport, tgt=ι_tgtport) 
        end
    end
    rem_parts!(xsum, :OP, parts(xsum, :OP))
    rem_parts!(xsum, :Bundle, parts(xsum, :Bundle))
    add_parts!(xsum, :Bundle, nparts(g, :Bundle))
    for op in parts(g, :OP)
        i = g[op, [:con, :box]]
        localport = findfirst(op .== incident(g, i, :box))
        @assert length(findall(op .== incident(g, i, :box))) == 1
        newop = legs(u.cocone)[i][:P](incident(xs[i], localport, :bun))
        # println("bundling: $op: $localport: $newop")
        add_parts!(xsum, :OP, length(newop), con=newop, bun=op)
    end
    return xsum
end


end