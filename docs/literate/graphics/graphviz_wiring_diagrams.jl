# # Drawing wiring diagrams in Graphviz
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/graphviz_wiring_diagrams.ipynb)
#
# Catlab can draw wiring diagrams using the `dot` program in
# [Graphviz](https://www.graphviz.org/). This feature requires that Graphviz be
# installed, but does not require any additional Julia packages.

using Catlab.WiringDiagrams, Catlab.Graphics

# ## Examples

# ### Symmetric monoidal category

using Catlab.Doctrines

A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A)
h = Hom(:h, otimes(A,B), otimes(A,B));

# To start, here are a few very simple examples.

to_graphviz(f)
#-
to_graphviz(compose(f,g))
#-
to_graphviz(otimes(f,g))

# In the next example, notice how Graphviz automatically "untwists" the double
# braiding to minimize edge crossings.

to_graphviz(compose(braid(A,A), otimes(f,f), braid(B,B)))

# Here is a larger composite morphism.

composite = compose(otimes(g,f), h, otimes(f,g))
to_graphviz(composite)

# By default, the wiring diagram is laid out from top to bottom. Other layout
# orientations can be requested, such as left-to-right or bottom-to-top:

to_graphviz(composite, orientation=LeftToRight)
#-
to_graphviz(composite, orientation=BottomToTop)

# When working with very large diagrams (larger than the ones shown here), it is
# sometimes convenient to omit the ports of the outer box and any wires attached
# to them.

to_graphviz(composite, outer_ports=false)

# ### Biproduct category

A, B = Ob(FreeBiproductCategory, :A, :B)
f = Hom(:f, A, B)
g = Hom(:g, B, A);

# By default, copies and merges are drawn the way they are represented
# internally, as multiple wires.

f1 = compose(mcopy(A), otimes(f,f))
to_graphviz(f1)
#-
f2 = compose(mcopy(A), otimes(f,f), mmerge(B))
to_graphviz(f2)

# To draw nodes for copies and merges, we need to add junctions to the wiring
# diagram.

to_graphviz(add_junctions!(to_wiring_diagram(f1)))
#-
to_graphviz(add_junctions!(to_wiring_diagram(f2)))

# ### Traced monoidal category

A, B, X, Y = Ob(FreeTracedMonoidalCategory, :A, :B, :X, :Y)
f = Hom(:f, otimes(X,A), otimes(X,B))

to_graphviz(trace(X, A, B, f))
#-
to_graphviz(trace(X, A, B, f), orientation=LeftToRight)
#-
g, h = Hom(:g, A, A), Hom(:h, B, B)

trace_naturality = trace(X, A, B, compose(otimes(id(X),g), f, otimes(id(X),h)))
to_graphviz(trace_naturality, orientation=LeftToRight)

# ## Custom styles

# The visual appearance of wiring diagrams can be customized by setting Graphviz
# [attributes](https://www.graphviz.org/doc/info/attrs.html) at the graph, node,
# edge, and cell levels. Graph, node, and edge attributes are described in the
# Graphviz documentation. Cell attributes are passed to the primary cell of the
# [HTML-like label](https://www.graphviz.org/doc/info/shapes.html#html) used for
# the boxes.

A, B, C = Ob(FreeSymmetricMonoidalCategory, :A, :B, :C)
f, g = Hom(:f, A, B), Hom(:g, B, C)

to_graphviz(compose(f,g),
  labels = true, label_attr=:headlabel,
  node_attrs = Dict(
    :fontname => "Courier",
  ),
  edge_attrs = Dict(
    :fontname => "Courier",
    :labelangle => "25",
    :labeldistance => "2",
  ),
  cell_attrs = Dict(
    :bgcolor => "lavender",
  )
)

# ## Output formats

# The function `to_graphviz` returns an object of a type `Graphviz.Graph`,
# representing a Graphviz graph as an abstract syntax tree. When displayed
# interactively, this object is automatically run through Graphviz and rendered
# as an SVG image. Sometimes it is convenient to perform this process manually,
# to change the output format or further customize the generated dot file.

# To generate a dot file, use the builtin pretty-printer. This feature does not
# require Graphviz to be installed.

using Catlab.Graphics: Graphviz

graph = to_graphviz(compose(f,g))
Graphviz.pprint(graph)

# Catlab provides a simple wrapper around the Graphviz command-line programs.
# For example, here is the JSON output for the graph.

import JSON

JSON.parse(Graphviz.run_graphviz(graph, format="json0"))
