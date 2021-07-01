module CPortGraphs
export ThCPortGraph, ThOpenCPortGraph, ThSymCPortGraph, ThOpenSymCPortGraph,
  CPortGraph, OpenCPortGraph, SymCPortGraph, OpenSymCPortGraph,
  ThBundledCPG, BundledCPG

using ...Theories, ...Present,  ...CategoricalAlgebra
import ...CategoricalAlgebra: migrate!
using ...Graphs
import ...Graphs.BasicGraphs: TheoryGraph
import ..DirectedWiringDiagrams: ocompose

@present ThCPortGraph(FreeSchema) begin
  Box::Ob
  Port::Ob
  Wire::Ob

  src::Hom(Wire, Port)
  tgt::Hom(Wire, Port)
  box::Hom(Port, Box)
end

@present ThOpenCPortGraph <: ThCPortGraph begin
  OuterPort::Ob
  con::Hom(OuterPort, Port)
end

@present ThSymCPortGraph <: ThCPortGraph begin
  inv::Hom(Wire, Wire)

  compose(inv,inv) == id(Wire)
  compose(inv,src) == tgt
  compose(inv,tgt) == src
end

@present ThOpenSymCPortGraph <: ThSymCPortGraph begin
  OuterPort::Ob
  con::Hom(OuterPort, Port)
end

""" Abstract type for circular port graphs.
"""
const AbstractCPortGraph = AbstractACSetType(ThCPortGraph)

""" A circular port graph.

Circular port graphs consist of boxes with ports connected by directed wires.
The ports are not seperated into inputs and outputs, so the "boxes" are actually
circular, hence the name.
"""
const CPortGraph = ACSetType(ThCPortGraph, index=[:box, :src, :tgt])

""" Abstract type for open circular port graphs.
"""
const AbstractOpenCPortGraph = AbstractACSetType(ThOpenCPortGraph)

""" An open circular port graph.

Open circular port graphs are circular port graphs with a distinguished set of
outer ports. They have a natural operad structure and can be seen as a
specialization of directed wiring diagrams.
"""
const OpenCPortGraph = ACSetType(ThOpenCPortGraph, index=[:box, :src, :tgt])

const AbstractSymCPortGraph = AbstractACSetType(ThSymCPortGraph)
const SymCPortGraph = ACSetType(ThSymCPortGraph, index=[:box, :src])

const AbstractOpenSymCPortGraph = AbstractACSetType(ThOpenSymCPortGraph)
const OpenSymCPortGraph = ACSetType(ThOpenSymCPortGraph, index=[:box, :src])
const OSCPGraph = OpenSymCPortGraph

function OpenCPortGraph(g::AbstractCPortGraph)
  x = OpenCPortGraph()
  copy_parts!(x, g)
  return x
end

function migrate!(g::AbstractGraph, cpg::AbstractCPortGraph)
  migrate!(g, cpg,
    Dict(:E=>:Wire, :V=>:Box),
    Dict(:src=>compose(ThCPortGraph[:src], ThCPortGraph[:box]),
         :tgt=>compose(ThCPortGraph[:tgt], ThCPortGraph[:box])))
end

function migrate!(pg::AbstractCPortGraph, opg::AbstractOpenCPortGraph)
  migrate!(pg, opg,
    Dict(:Box=>:Box, :Port=>:Port, :Wire=>:Wire),
    Dict(:src=>:src, :tgt=>:tgt, :box=>:box))
end

function migrate!(pg::AbstractCPortGraph, g::AbstractGraph)
  migrate!(pg, g,
    Dict(:Box=>:V, :Port=>:V, :Wire=>:E),
    Dict(
      :box=>id(TheoryGraph[:V]),
      :src=>TheoryGraph[:src],
      :tgt=>TheoryGraph[:tgt],
    )
  )
end

function migrate!(og::AbstractOpenCPortGraph, g::AbstractCPortGraph)
  migrate!(og, g,
    Dict(:Box=>:Box, :Port=>:Port, :Wire=>:Wire, :OuterPort=>:Port),
    Dict(
      :src=>:src,
      :tgt=>:tgt,
      :box=>:box,
      :con=>id(ThCPortGraph[:Port]),
    )
  )
end
migrate!(og::AbstractOpenCPortGraph, g::AbstractGraph) =
  migrate!(og, migrate!(CPortGraph(),g))

function migrate!(pg::AbstractSymCPortGraph, g::AbstractSymmetricGraph)
  migrate!(pg, g,
    Dict(:Box=>:V, :Port=>:V, :Wire=>:E),
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
  for e in parts(g, :Wire)
    s, t = g[e, :src], g[e, :tgt]
    sbox, tbox = g[s, :box], g[t, :box]
    localport_src = findfirst(s .== incident(g, sbox, :box))
    localport_tgt = findfirst(t .== incident(g, tbox, :box))
    ι_srcport = legs(u.cocone)[sbox][:Port](xs[sbox][localport_src, :con])
    ι_tgtport = legs(u.cocone)[tbox][:Port](xs[tbox][localport_tgt, :con])
    add_part!(sum, :Wire; src=ι_srcport, tgt=ι_tgtport)
  end
  rem_parts!(sum, :OuterPort, parts(sum, :OuterPort))
  for op in parts(g, :OuterPort)
    i = g[op, [:con, :box]]
    j = findfirst(g[op, :con] .== incident(g, i, :box))
    localport = xs[i][j, :con]
    newop = legs(u.cocone)[i][:Port](localport)
    add_parts!(sum, :OuterPort, 1, con=newop)
  end
  return sum
end

@present ThBundledCPG <: ThOpenCPortGraph begin
  Bundle::Ob
  bun::Hom(OuterPort, Bundle)
end

const AbstractBundledCPG = AbstractACSetType(ThBundledCPG)
const BundledCPG = ACSetType(ThBundledCPG, index=[:box, :src, :tgt, :bun])

function migrate!(b::AbstractBundledCPG, g::AbstractOpenCPortGraph)
  migrate!(b,g,
    Dict(:Box=>:Box, :Port=>:Port, :Wire=>:Wire, :OuterPort=>:OuterPort,
         :Bundle=>:OuterPort),
    Dict(:src=>:src, :tgt=>:tgt, :box=>:box,
         :con=>:con, :bun=>id(ThOpenCPortGraph[:OuterPort])))
end

function BundledCPG(g::AbstractOpenCPortGraph)
  bg = BundledCPG()
  copy_parts!(bg, g)
  return bg
end

function ocompose(g::AbstractBundledCPG, xs::Vector)
  u = coproduct(xs)
  xsum=apex(u)
  for e in parts(g, :Wire)
    s, t = g[e,:src], g[e,:tgt]
    sbox, tbox = g[s, :box], g[t, :box]
    localport_src = findfirst(s .== incident(g, sbox, :box))
    localport_tgt = findfirst(t .== incident(g, tbox, :box))
    @assert length(findall(s .== incident(g, sbox, :box))) == 1
    @assert length(findall(t .== incident(g, tbox, :box))) == 1

    sbun = incident(xs[sbox], localport_src, :bun)
    tbun = incident(xs[tbox], localport_tgt, :bun)
    for thread in zip(sbun, tbun)
      ι_srcport = legs(u.cocone)[sbox][:Port](xs[sbox][thread[1], :con])
      ι_tgtport = legs(u.cocone)[tbox][:Port](xs[tbox][thread[2], :con])
      add_part!(xsum, :Wire; src=ι_srcport, tgt=ι_tgtport)
    end
  end
  rem_parts!(xsum, :OuterPort, parts(xsum, :OuterPort))
  rem_parts!(xsum, :Bundle, parts(xsum, :Bundle))
  add_parts!(xsum, :Bundle, nparts(g, :Bundle))
  for op in parts(g, :OuterPort)
    i = g[op, [:con, :box]]
    localport = findfirst(op .== incident(g, i, :box))
    @assert length(findall(op .== incident(g, i, :box))) == 1
    newop = legs(u.cocone)[i][:Port](incident(xs[i], localport, :bun))
    add_parts!(xsum, :OuterPort, length(newop), con=newop, bun=op)
  end
  return xsum
end

end
