# # Drawing graphs in Graphviz
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/graphics/graphviz_graphs.ipynb)
#
# All of the basic graph types provided by the Catlab `Graphs` module can be
# drawn using [Graphviz](https://www.graphviz.org/). By default, "directed"
# graph types (`Graph`, `ReflexiveGraph`) are drawn using the `dot` program and
# "undirected" graph types (`SymmetricGraph`, `HalfEdgeGraph`) are drawn using
# the `neato` program.

using Catlab.Graphs, Catlab.Graphics

# ## Drawing basic graphs

g = cycle_graph(Graph, 3)
to_graphviz(g)
#-
sg = cycle_graph(SymmetricGraph, 3)
to_graphviz(sg)

# Node and edge IDs can be shown by setting `node_labels=true` and
# `edge_labels=true`, or a data attribute can be used as a label by setting
# `node_labels=:my_vertex_attr` and `edge_lables=:my_edge_attr`.

to_graphviz(g, node_labels=true, edge_labels=true)

# Graph-level, node-level, and edge-level [Graphviz
# attributes](https://graphviz.org/doc/info/attrs.html) can be supplied using
# the `graph_attrs`, `node_attrs`, and `edge_attrs` keyword arguments.

to_graphviz(g, node_attrs=Dict(:color => "cornflowerblue"),
            edge_attrs=Dict(:style => "dotted"))

# ## Drawing graph homomorphisms
#
# Graph homomorphsims (`ACSetTransformation`s between graphs) can also be drawn
# using Graphviz, in several different styles.

using Catlab.CategoricalAlgebra

f = homomorphism(cycle_graph(Graph, 4), complete_graph(Graph, 2))

# By default, the domain and codomain graph are both drawn, as well the vertex
# mapping between them.

to_graphviz(f)

# To see the edge mapping, which is not necessarily unique in the presence of
# the multiple edges, colors can be used.

to_graphviz(f, edge_colors=true)

# Alternatively, the graph homomorphism can be depicted by drawing only the
# domain graph and coloring its nodes and edges. By default, setting
# `draw_codom=false` sets both `node_colors=true` and `edge_colors=true`.

to_graphviz(f, draw_codom=false)
#-
to_graphviz(f, draw_codom=false, edge_colors=false)

# ## Drawing maps between finite sets
# 
# It is also possible to visualize maps between finite sets (`FinFunction`s between
# `FinSet`s) using Graphviz.

using Catlab.CategoricalAlgebra.FinSets

A = FinSet(4)
B = FinSet(3)
f = FinFunction([1,2,2,3], A, B)

# By default the mapping is shown by edges between the domain and codomain
# subgraphs. One can turn this off with `draw_edge=false` if desired. By
# using `elem_colors=true`, the mapping will be denoted with colors instead of
# or in addition to edges. If using colors one can additionally use 
# `edge_colors=true` to color the edges between subgraphs.

to_graphviz(f)

# For example:

to_graphviz(f, elem_colors=true, edge_colors=true)

# Elements in the sets can be labeled by setting `elem_labels=true`. Additionally
# there are keyword args `invis_edge_dom` and `invis_edge_codom` which accept
# boolean values. If set to `true` then invisible edges are drawn between elements
# in the subgraph for which the argument was selected. This can help align the
# subgraphs when trying to achieve a desired "look" for the graphic, especially
# when combined with the graph attribute [`rankdir`](https://graphviz.org/docs/attrs/rankdir/).

to_graphviz(
    f, elem_colors=true, edge_colors=true,
    invis_edge_dom=true, invis_edge_codom=true,
    graph_attrs=Dict(:rankdir => "TB")
)