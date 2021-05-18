using Catlab.CategoricalAlgebra.CSets

#------------------------------------------------
# automorphisms
#------------------------------------------------

"""
want to compute these for CSets
    https://ncatlab.org/nlab/show/core-natural+transformation
"""

CDict = Dict{Symbol, Vector{Int}}

"""Compute all automorphisms of a CSet"""
function autos(g::CSet) :: Set{CDict}
    res = Set{CDict}()
    seen = Set{CDict}()
    # Initial coloring - everything is 1
    cs = Dict([comp=>ones(Int, nparts(g, comp))
               for comp in keys(g.tables)])
    branch!(g, cs, 1, res, seen)
    @assert Dict(:x1=>[1,3,2]) in res
    return res
end

"""Take a random color that has multiple nodes and split on it"""
function branch!(g::CSet, cs::CDict, depth::Int, res::Set{CDict}, seen::Set{CDict})
    println("\n$depth BRANCHING $cs\nseen $([x[:x1] for x in seen])\n")
    comps = collect(keys(g.tables))
    change = false
    for comp in comps  # take a random component
        if length(cs[comp]) != length(Set(cs[comp])) # check if it has a color w/ more than one element
            max_color = maximum(cs[comp])
            color_set = [Set() for _ in 1:max_color]
            for (ind, color) in enumerate(cs[comp])
                push!(color_set[color],ind)
            end
            change=true
            for indices in filter(x->length(x)>1,color_set)
                for index in indices
                    updated_cs = update_colors(g, deepcopy(cs), comp, index) # result of split
                    if !(updated_cs in seen) # result is new
                        push!(seen, updated_cs)
                        branch!(g, updated_cs, depth+1, res, seen)
                    end
                end
            end
        end
    end
    if !change
        push!(res, cs)
    end
end

"""
Supsicious to leave the (arbitrary) first batch unchanged but set all
others to a new value?
"""
function refine_color(g::CSet, cs::CDict, arrow_ind::Int)::Pair{CDict, Bool}
    comps, arr, src, tgt = typeof(g).parameters[1].parameters
    arrow = arr[arrow_ind]
    source, target = [comps[x[arrow_ind]] for x in [src, tgt]]
    change = false
    target_max_color = maximum(cs[target])
    source_max_color = maximum(cs[source])
    # partition source table by # of each color that is touched through arrow
    counts = [zeros(Int, target_max_color) for _ in 1:nparts(g,source)]
    for (color, preimage) in zip(cs[target], g.indices[arrow])
        for elem in preimage
            # println("$counts $elem $color")
            counts[elem][color] += 1
        end
    end
    # condense [col1=2, col2=4,col3=0,...] info into a single value
    hshs = map(hash, counts)

    # Group the elements of the source table by color
    source_parts = [Set{Int}() for _ in 1:source_max_color]
    for (source_elem, color) in enumerate(cs[source])
        push!(source_parts[color], source_elem)
    end

    # For each color in the source, we might discover that we
    # need more colors. `color_offset` remembers how many colors
    # we've added as we iterate through all source colors
    color_offset = 1
    # Look at the colors that could potentially have a conflict
    for part in filter(x->length(x)>1, source_parts)
        # get the arrow-color-profile of each source elem of this color
        subparts = Dict()
        for source_elem in part
            hsh = hshs[source_elem]
            if haskey(subparts, hsh)
                push!(subparts[hsh], source_elem)
            else
                subparts[hsh] = Set([source_elem])
            end
        end

        for source_elems in collect(values(subparts))[2:end] # first partition keeps label
            for source_elem in source_elems
                cs[source][source_elem] = source_max_color + color_offset
            end
            color_offset += 1
            change = true
        end
    end
    return cs => change
end

function refine_colors(g::CSet, cs::CDict)::CDict
    n_arrow = length(typeof(g).parameters[1].parameters[2])
    change = true
    n=0
    while change
        change = false
        for i in 1:n_arrow
            cs, changed = refine_color(g, cs, i)
            change = change || changed
        end
        n+=1
    end
    # println("refined in $n iterations")
    return cs
end

"""Differentiate elements by how many nodes of each color they touch"""
function update_colors(g::CSet, cs::CDict, tbl::Symbol, val::Int)::CDict
    # println("UPDATING tbl $tbl #$val - coloring is $cs")
    cs[tbl][val] = maximum(cs[tbl]) + 1
    return refine_colors(g, cs)
end

"""Apply a coloring to a Cset to get an isomorphic cset"""
function apply_automorphism(c::CSet,d::CDict)::CSet
    new = deepcopy(c)
    tabs, arrs, srcs, tgts = (typeof(c).parameters[1]).parameters
    for (arr, srci, tgti) in zip(arrs,srcs,tgts)
        src, tgt =  [tabs[x] for x in [srci, tgti]]
        set_subpart!(new, d[src],arr, d[tgt][c[arr]])
    end
    return new
end

function canonical_iso(g::CSet)::CSet
    # println("CALCULATING canon iso of $g")
    isos = sort([apply_automorphism(g, Dict(a)) for a in brute(g)], by=string)
    return isempty(isos) ? g : isos[1]
end
function canonical_hash(g::CSet)::UInt64
    return hash(string(canonical_iso(g)))
end

function direct_canon(g::CSet)::CSet
    tabs, arrs, srcs, tgts = (typeof(g).parameters[1]).parameters
    # prefer arrows that point to a table that's the source for many arrows
    order = sort(1:length(arrs), by=x->count(y->y==tgts[x], srcs))
    srcarrs = [[e for (e,s) in enumerate(srcs) if s==i] for i in order]
    arr_order = sort(eachindex(arrs), by=a->count(x->x==a,srcs), rev=true)

    # the state is the automorphism from the minimal (lexigraphic) automorph
    # to the particular g that is used
    # the first term is the data for the FKs which gets ordered.
    state = ([zeros(nparts(g,src)) for src in srcs],
             [Set{Int}(1:nparts(g,t)) for t in 1:length(tabs)])

    preimg = [g.indices[a] for a in arrs]

    function branch(state)
        arr_asgn, tab_asgn = state
        for arr_ind in arr_order
            arr = arrs[arr_ind]
            src,tgt = srcs[arr],tgts[arr]
            asgn = Set(arr_asgn[arr])
            for i in 1:nparts(g,src)
                if asgn[i] == 0
                    for next_ind in sort(collect(setdiff(1:nparts(g,tgt), asgn)))
                        new_asgn = deepcopy(asgn)
                        new_asgn[tab][i]=next_ind
                        res = propagate!((new_asgn, tab_asgn), arr, i)
                        if !(res===nothing)
                            return branch(res)
                        end
                    end
                    @assert false
                end
            end
        end
        return state
    end
    # Given that tab[arr][i] has just been set, what have we learned?
    function propagate!(state, arr, i)
        # apply heuristics to rule out possibilities from state
        arr_asgn, tab_asgn = state

        src, tgt = srcs[arr], tgts[arr]
        total_arrows_to_i = [src_ind for (src_ind, val) in enumerate(arr_asgn[arr]) if val == i]

        impossible_targets = [ind for (ind, pre) in enumerate(preimg[arr])
                              if length(pre) <= length(total_arrows_to_i)]
        state[tgt][i] = setdiff(state[tgt][i], impossible_targets)
        if isempty(state[tgt][i])
            return nothing
        else
            return arr_asgn, tab_asgn
        end
    end
    return branch(state)
end

function brute(g::CSet)::Set{CDict}
    tabs, arrs, srcs, tgts = (typeof(g).parameters[1]).parameters
    ntab = length(tabs)
    # uncomment to verify brute is not the cause of bottleneck
    return Set([Dict([t=>collect(1:(nparts(g,t))) for t in tabs])])
    srcarrs = [[e for (e,s) in enumerate(srcs) if s==i] for i in 1:ntab]
    function test_combo(comb)::Bool
        for src in 1:ntab
            #println("src $src ($(tabs[src]))")
            srcperm = comb[src]
            for arr in srcarrs[src]
                #println("arr $arr ($(arrs[arr]))")
                mapping = g[arrs[arr]]
                tgtperm = comb[tgts[arr]]
                for i in 1:nparts(g, src)
                    #println("$i mapping $mapping, srcperm $srcperm tgtperm $tgtperm")
                    if mapping[srcperm[i]] != tgtperm[mapping[i]]
                        return false
                    end
                end
            end
        end
        return true
    end
    res = Set{CDict}()
    perms = [collect(permutations(1:nparts(g,s))) for s in tabs]
    for combo in Iterators.product(perms...)
        if test_combo(combo)
            push!(res, Dict(zip(tabs,combo)))
        end
    end
    return res
end