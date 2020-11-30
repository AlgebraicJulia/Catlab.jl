module CPortGraphs
using ...Theories
using ...CategoricalAlgebra
import ...CategoricalAlgebra.CSets: migrate!
using ...Present
using ...Graphs
import ...Graphs.BasicGraphs: TheoryGraph
import ..DirectedWiringDiagrams: ocompose

export ThCPortGraph, ThOpenCPortGraph, ThSymCPortGraph, ThOpenSymCPortGraph, ThBundledCPG,
  CPortGraph, OpenCPortGraph, SymCPortGraph, OpenSymCPortGraph, BundledCPG


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

const AbstractCPortGraph = AbstractACSetType(ThCPortGraph)
const CPortGraph = ACSetType(ThCPortGraph, index=[:box, :src, :tgt])

const AbstractOpenCPortGraph = AbstractACSetType(ThOpenCPortGraph)
const OpenCPortGraph = ACSetType(ThOpenCPortGraph, index=[:box, :src, :tgt])

const AbstractSymCPortGraph = AbstractACSetType(ThSymCPortGraph)
const SymCPortGraph = ACSetType(ThSymCPortGraph, index=[:box, :src])

const AbstractOpenSymCPortGraph = AbstractACSetType(ThOpenSymCPortGraph)
const OpenSymCPortGraph = ACSetType(ThOpenSymCPortGraph, index=[:box, :src])
const OSCPGraph = OpenSymCPortGraph

function OpenCPortGraph(g::AbstractCPortGraph)
    x = OpenCPortGraph()
    copy_parts!(x, g, W=parts(g, :W), P=parts(g, :P), B=parts(g, :B))
    return x
end

function migrate!(g::Graph, cpg::AbstractCPortGraph)
    migrate!(g, cpg,
    Dict(:E=>:W, :V=>:B),
    Dict(
        :src=>compose(ThCPortGraph[:src], ThCPortGraph[:box]),
        :tgt=>compose(ThCPortGraph[:tgt], ThCPortGraph[:box])))
end

function migrate!(pg::AbstractCPortGraph, opg::AbstractOpenCPortGraph)
    migrate!(pg, opg,
        Dict(:B=>:B, :P=>:P, :W=>:W),
        Dict(:src=>:src, :tgt=>:tgt, :box=>:box)
    )
end

function migrate!(pg::AbstractCPortGraph, g::Graph)
    migrate!(pg, g,
      Dict(:B=>:V, :P=>:V, :W=>:E),
      Dict(
          :box=>id(TheoryGraph[:V]),
          :src=>TheoryGraph[:src],
          :tgt=>TheoryGraph[:tgt],
      )
    )
end

function migrate!(og::AbstractOpenCPortGraph, g::AbstractCPortGraph)
    migrate!(og, g,
        Dict(:B=>:B, :P=>:P, :W=>:W, :OP=>:P),
        Dict(
            :src=>:src,
            :tgt=>:tgt,
            :box=>:box,
            :con=>id(ThCPortGraph[:P])
        ))
end
migrate!(og::AbstractOpenCPortGraph, g::Graph) = migrate!(og, migrate!(CPortGraph(),g))

function migrate!(pg::AbstractSymCPortGraph, g::SymmetricGraph)
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

function ocompose(g::AbstractOpenCPortGraph, xs::Vector)
    u = coproduct(xs)
    sum = apex(u)
    for e in parts(g, :W)
        s = g[e, :src]
        t = g[e, :tgt]
        sbox = g[s, :box]
        tbox = g[t, :box]
        localport_src = findfirst(s .== incident(g, sbox, :box))
        localport_tgt = findfirst(t .== incident(g, tbox, :box))
        ι_srcport = legs(u.cocone)[sbox][:P](xs[sbox][localport_src, :con])
        ι_tgtport = legs(u.cocone)[tbox][:P](xs[tbox][localport_tgt, :con])
        add_part!(sum, :W; src=ι_srcport, tgt=ι_tgtport)
    end
    rem_parts!(sum, :OP, parts(sum, :OP))
    for op in parts(g, :OP)
        i = g[op, [:con, :box]]
        j = findfirst(g[op, :con] .== incident(g, i, :box))
        localport = xs[i][j, :con]
        newop = legs(u.cocone)[i][:P](localport)
        add_parts!(sum, :OP, 1, con=newop)
    end
    return sum
end

@present ThBundledCPG <: ThOpenCPortGraph begin
    Bundle::Ob
    bun::Hom(OP, Bundle)
end

const AbstractBundledCPG = AbstractACSetType(ThBundledCPG)
const BundledCPG = ACSetType(ThBundledCPG, index=[:box, :src, :tgt, :bun])

migrate!(b::AbstractBundledCPG, g::AbstractOpenCPortGraph) = migrate!(b,g,
    Dict(:B=>:B, :P=>:P, :W=>:W, :OP=>:OP, :Bundle=>:OP),
    Dict(:src=>:src, :tgt=>:tgt, :box=>:box,
         :con=>:con, :bun=>id(ThOpenCPortGraph[:OP]))
)

function BundledCPG(g::AbstractOpenCPortGraph)
    bg = BundledCPG()
    copy_parts!(bg, g,
      W=parts(g,:W), P = parts(g,:P), B=parts(g, :B), OP=parts(g,:OP))
    return bg
end

function ocompose(g::AbstractBundledCPG, xs::Vector)
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

        sbun = incident(xs[sbox], localport_src, :bun)
        tbun = incident(xs[tbox], localport_tgt, :bun)
        for thread in zip(sbun, tbun)
            ι_srcport = legs(u.cocone)[sbox][:P](xs[sbox][thread[1], :con])
            ι_tgtport = legs(u.cocone)[tbox][:P](xs[tbox][thread[2], :con])
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
        add_parts!(xsum, :OP, length(newop), con=newop, bun=op)
    end
    return xsum
end


end
