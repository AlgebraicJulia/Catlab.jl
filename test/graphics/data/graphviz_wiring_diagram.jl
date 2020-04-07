using Catlab.WiringDiagrams

f = singleton_diagram(Box(:f, [:A], [:A]))
g = singleton_diagram(Box(:g, [:B], [:B]))
h = singleton_diagram(Box(:h, [:A,:B], [:C]))
diagram = compose(otimes(f,g),h)
