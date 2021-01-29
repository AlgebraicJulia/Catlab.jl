module Presentations

using ...Present
using ...Theories
using ..BasicGraphs
using ..PropertyGraphs

index_of(pres::Presentation, x::Symbol) = pres.generator_name_index[x].second

function presentation_to_graph(pres::Presentation)
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
    set_eprop!(g,i+length(homs),:label,string(nameof(attrs)))
  end
  set_gprop!(g,:graph,Dict(:rankdir => "LR"))
  g
end

end
