# # Wiring Diagrams as Attributed C-Sets
# Catlab supports many different flavors of diagrammatic syntax. These support the different combinatorial data structures that we use for representing categorical constructions. We will discuss DirectedWiringDiagrams, UndirectedWiringDiagrams, and CPortGraphs in this document.
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Programs
using Catlab.WiringDiagrams

draw(d::WiringDiagram) = to_graphviz(d,
  orientation=LeftToRight,
  labels=true, label_attr=:xlabel,
  node_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  ),
  edge_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  )
)

# ## Directed Wiring Diagrams

# DWDs are used to represent the morphisms in a symmetric monoidal category. You can get started by presenting a `FreeSymmetricMonoidalCategory` with the `@present` macro.
@present P(FreeSymmetricMonoidalCategory) begin
  (A,B,C,D)::Ob
  f::Hom(A,B)
  g::Hom(B,A)
  h::Hom(A⊗B, C)
  k::Hom(C,D⊗A)
end
generators(P)

# these presentations are very syntactic objects and expose an API for manipulating expressions.
for g in generators(P)
  println("$g is a $(gat_typeof(g)) with arguments $(gat_type_args(g))")
end


homs_P = filter(generators(P)) do g
  gat_typeof(g) == :Hom
end

map(homs_P) do f
  "$f: $(dom(f)) → $(codom(f))"
end

# when we want to work with big expressions in an SMC, the tree structure inherent to trees is too restrictive, and we want to move to a port-graph structure called `DirectedWiringDiagrams`. 
wd = @program P (a::A, b::B) begin
  c = h(a,b)
  return k(c)
end

draw(wd)

wd = @program P (a::A, b::B) begin
  c = h(a,b)
  d,a₁ = k(c)
  return d, f(a₁)
end
draw(wd)

# You can terminate wires by just not returning them.
wd = @program P (a::A, b::B) begin
  c = h(a,b)
  d,a₁ = k(c)
  return f(a₁)
end
draw(wd)

# The underlying data of a wiring diagram is combinatorial. That means we can represent it as a C-Set
wd.diagram

# The schema of for wiring diagrams is called TheoryAttributedWiringDiagrams and is a little overwhelming, so we can explore how to build it up with C-Set schema inheritance.
to_graphviz(WiringDiagrams.DirectedWiringDiagrams.TheoryAttributedWiringDiagram)

# From the file Catlab/src/WiringDiagrams/Directed.jl
# ```julia
# @present TheoryWiringDiagram(FreeSchema) begin
#   Box::Ob
#   (InPort, OutPort, OuterInPort, OuterOutPort)::Ob
#   (Wire, InWire, OutWire, PassWire)::Ob
  
#   src::Hom(Wire, OutPort)
#   tgt::Hom(Wire, InPort)
#   in_src::Hom(InWire, OuterInPort)
#   in_tgt::Hom(InWire, InPort)
#   out_src::Hom(OutWire, OutPort)
#   out_tgt::Hom(OutWire, OuterOutPort)
#   pass_src::Hom(PassWire, OuterInPort)
#   pass_tgt::Hom(PassWire, OuterOutPort)

#   in_port_box::Hom(InPort, Box)
#   out_port_box::Hom(OutPort, Box)
# end

# @abstract_acset_type AbstractWiringDiagram <: AbstractGraph

# @present TheoryTypedWiringDiagram <: TheoryWiringDiagram begin
#   PortValue::AttrType
#   in_port_type::Attr(InPort, PortValue)
#   out_port_type::Attr(OutPort, PortValue)
#   outer_in_port_type::Attr(OuterInPort, PortValue)
#   outer_out_port_type::Attr(OuterOutPort, PortValue)
# end

# @present TheoryAttributedWiringDiagram <: TheoryTypedWiringDiagram begin
#   WireValue::AttrType
#   BoxValue::AttrType
#   BoxType::AttrType

#   value::Attr(Box, BoxValue)
#   box_type::Attr(Box, BoxType)
#   wire_value::Attr(Wire, WireValue)
#   in_wire_value::Attr(InWire, WireValue)
#   out_wire_value::Attr(OutWire, WireValue)
#   pass_wire_value::Attr(PassWire, WireValue)
# end
# ```

# The bare minimum diagram language is:
to_graphviz(WiringDiagrams.DirectedWiringDiagrams.TheoryWiringDiagram)

# And then you can add back in the types.
to_graphviz(WiringDiagrams.DirectedWiringDiagrams.TheoryTypedWiringDiagram)

#Layout is hard, so if you want to understand the `TheoryAttributedWiringDiagrams`, you should do the layout by hand as an exercise.


# We can create our own version of the theory of DWDs to see how it works:
@present MyTheoryWiringDiagram(FreeSchema) begin
  Box::Ob
  (InPort, OutPort, OuterInPort, OuterOutPort)::Ob
  (Wire, InWire, OutWire, PassWire)::Ob
  
  src::Hom(Wire, OutPort)
  tgt::Hom(Wire, InPort)
  in_src::Hom(InWire, OuterInPort)
  in_tgt::Hom(InWire, InPort)
  out_src::Hom(OutWire, OutPort)
  out_tgt::Hom(OutWire, OuterOutPort)
  pass_src::Hom(PassWire, OuterInPort)
  pass_tgt::Hom(PassWire, OuterOutPort)

  in_port_box::Hom(InPort, Box)
  out_port_box::Hom(OutPort, Box)
end

# Then we create a new ACSet type for them:
@acset_type MyWiringDiagramACSet(MyTheoryWiringDiagram,
  index=[:src, :tgt, :in_src, :in_tgt, :out_src, :out_tgt, :pass_src, :pass_tgt]) <: WiringDiagrams.DirectedWiringDiagrams.AbstractWiringDiagram

# We get the `@acset` macro from Catlab and can create DWDs by hand. It is very tedious, which is why the `@program` macro exists!
md = @acset MyWiringDiagramACSet begin
  Box = 3
  InPort = 6
  OutPort = 3
  Wire = 3
  src = [1,2,3]
  tgt = [3,4,5]
  in_port_box = [1,1,2,2,3,3]
  out_port_box = [1,2,3]
end


# ## Undirected Wiring Diagrams
to_graphviz(WiringDiagrams.UndirectedWiringDiagrams.TheoryUWD)

# UWDs are combinatorial syntax for relations
uwd = @relation (x, y, z) begin
  R(x,y)
  S(y,z)
end

# These UWDs are draw with circular boxes and undirected wires. Note that since all wires go from junction to port, they are not *symmetric* wires.
to_graphviz(uwd, junction_labels=:variable, box_labels=:name)

# By adding more relations we can get bigger relations.
uwd₂ = @relation (x, z) begin
  R(x,y)
  S(y,z)
  T(x,z,y)
end

# Not all of the junctions have to be exposed to the outside world.
to_graphviz(uwd₂, junction_labels=:variable, box_labels=:name)

# ## Circular Port Graphs
# CPGs are the natural data structure for representing process of interconnected systems that share information along wires, but have to distinguish between their neighbors.
to_graphviz(ThCPortGraph)

# They are also a kind of CSet, so we can use the `@acset` macro to construct them.
cpg = @acset CPortGraph begin
  Box = 3
  Port = 6
  Wire = 5

  box = [1,1,2,2,3,3]
  src = [1,2,5,2,6]
  tgt = [3,4,2,4,1]
end

# the layout for CPGs is not great with graphviz.
to_graphviz(cpg, port_labels=true, graph_attrs=Dict("nodesep"=>"2", "ranksep"=>"2"))
