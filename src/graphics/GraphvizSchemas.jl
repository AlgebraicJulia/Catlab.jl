""" Visualization of Schemas for Acsets
"""
module GraphvizSchemas
export visualize_schema

using ...Present
using ...Theories
using ...Graphs.BasicGraphs
using ...Graphs.PropertyGraphs
using ..GraphvizGraphs

""" Draw a graph representing the schema
"""
function visualize_schema(pres::Presentation{Schema})
  obs,homs,datas,attrs = generators.(Ref(pres), [:Ob,:Hom,:Data,:Attr])
  g = PropertyGraph{Any}()

  add_vertices!(g,length(obs))
  for (i,ob) in enumerate(obs)
    set_vprop!(g,i,:label,string(nameof(ob)))
    set_vprop!(g,i,:shape,"plain")
    set_vprop!(g,i,:margin,"2")
  end

  add_vertices!(g,length(datas))
  for (i,data) in enumerate(datas)
    set_vprop!(g,i+length(obs),:label,string(nameof(data)))
  end

  add_edges!(g,
             index_of.(Ref(pres), nameof.(dom.(homs))),
             index_of.(Ref(pres), nameof.(codom.(homs))))
  for (i,hom) in enumerate(homs)
    set_eprop!(g,i,:label,string(nameof(hom)))
  end
  
  add_edges!(g,
             index_of.(Ref(pres), nameof.(dom.(attrs))),
             length(obs) .+ index_of.(Ref(pres), nameof.(codom.(attrs))))
  for (i,attr) in enumerate(attrs)
    set_eprop!(g,i+length(homs),:label,string(nameof(attr)))
  end

  set_gprop!(g,:graph,Dict(:rankdir => "LR"))

  to_graphviz(g)
end

end
