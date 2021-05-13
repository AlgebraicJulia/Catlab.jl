using Catlab.CategoricalAlgebra.CSets
using Catlab.Graphs

g = cycle_graph(Graph, 3)
h = Graph(3)
add_edges!(h,[2,3,1],[3,1,2])


# Compute the automorphisms
function autos(g::CSet) :: Set{Dict}
function branch(g::CSet, cs::Dict) :: Set{Dict}
    res = Set()
    comps = keys(g.tables)
    cs = Dict([comp=>ones(Int, length(t)) for (comp, t)
               in zip(comps, g.tables)])
    for comp in comps
        if length(cs[comp])!=length(Set(cs[comp]))
            seen = Set()
            for (i, c) in enumerate(cs[comp])
                if c in seen
                    updated_cs = update(g, deepcopy(cs), comp, i)
                    union!(res, branch(g, updated_cs))
                else
                    push!(seen, c)
                end
            end
        end
    end
    return res
end

function update(g::CSet, cs::Dict, tbl::Symbol, val::Int)::Set{Dict}
    println("branch with $tbl#$val")
    comps, arr, src, tgt = typeof(g).parameters[1].parameters

    incident = Dict([comp=>([(a,comps[s]) for (a,s,t) in zip(arr,src,tgt)
                     if t == i]) for (i, comp) in enumerate(comps)])

    new_color = maximum(cs[tbl]) + 1
    cs[tbl][val] = new_color

    # propagate info for everything incident to tbl
    for (arrow, srctab) in incident[tbl]
        # partition source table by # of each color that is touched through arrow
        counts = [zeros(Int, new_color) for _ in  1:length(g.tables[srctab])]
        for (color, preimage) in zip(cs[tbl], g.indices[arrow])
            for elem in preimage
                counts[elem][color] += 1
            end
        end
        hshs = map(hash, counts)
        parts = Dict([h=>[] for h in hshs])
        for (i,h) in enumerate(hshs)
            push!(parts[h],i)
        end
        old_max = maximum(cs[srctab])
        orig_parts = [[i for (i,col) in enumerate(cs[srctab])
                      if col==c] for c in 1:old_max]
        # change colors if needed
        for part in filter(x->length(x)>1, orig_parts)
            parthsh = [hshs[i] for i in part]
            hshdict = Dict([h=>[] for h in collect(Set(parthsh))])
            for (h, i) in zip(parthsh, part)
                push!(hshdict[h],i)
            end
            for (offset, is) in enumerate(collect(values(hshdict))[2:end]) # first partition keeps label
                cs[srctab][is] .= old_max + offset
            end
        end
    end
    return cs
end

res=  autos(g)