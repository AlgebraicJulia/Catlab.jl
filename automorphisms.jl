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

function direct_canon(g::CSet{CD})::CSet where {CD}
    tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
    src_arrs = [[a_ind for (a_ind, src_tab) in enumerate(srcs) if src_tab==tab] for tab in eachindex(tabs)]
    # the state is the automorphism from the minimal (lexigraphic) automorph
    # to the particular g that is used
    # the first term is the data for the FKs which gets ordered.
    state = ([zeros(Int, nparts(g,src)) for src in srcs],
             [let n=nparts(g,t); [Set{Int}(1:n) for _ in 1:n] end for t in 1:length(tabs)])

    n_preimg = [map(length,g.indices[a]) for a in arrs]

    function branch(state)
        arr_asgn, tab_asgn = state
        println("BRANCHING WITH STATE $arr_asgn\n\t$(join(map(collect,tab_asgn),"\n\t")))")
        @assert arr_asgn[2][4] == 0 || (arr_asgn[1][3], arr_asgn[2][3]) != (2,1)
        for (tab_ind, _) in enumerate(tabs)
            for (ith_arr, arr) in enumerate(src_arrs[tab_ind])
                src,tgt = srcs[arr],tgts[arr]
                for i in 1:nparts(g,src)
                    if arr_asgn[arr][i] == 0
                        for next_ind in 1:nparts(g,tgt)
                            new_asgn = deepcopy(arr_asgn)
                            new_asgn[arr][i]=next_ind
                            res = propagate_fk!((new_asgn, deepcopy(tab_asgn)), ith_arr, arr, i)
                            if !(res===nothing)
                                return branch(res)
                            end
                        end
                        @assert false
                    end
                end
            end
        end
        return state
    end
    function propagate_pk!(state, tab, tab_i)
        arr_asgn, tab_asgn = state
        noncanonical_index, = tab_asgn[tab][tab_i]
        println("ENTERING PROPAGATE PK (just discovered $(tabs[tab])#$tab_i ↦ $noncanonical_index) \n\twith tab_asgn\n\t\t$(join(map(collect,tab_asgn),"\n\t\t"))")
        for (tab_ind, tab_poss) in enumerate(tab_asgn[tab])
            if tab_ind!=tab_i
                deleted = noncanonical_index in tab_poss
                if deleted
                    println("\tb/c $(tabs[tab])#($tab_i) is fixed in the canonical graph to be value $noncanonical_index, $tab#$tab_ind in the canonical graph cannot be $noncanonical_index")
                    delete!(tab_poss, noncanonical_index)
                    n = length(tab_poss)
                    if n == 0
                        println("UNSAT")
                        return nothing
                    elseif n == 1
                        res = propagate_pk!((arr_asgn, tab_asgn), tab, tab_ind)
                        if res === nothing
                            return nothing
                        else
                            arr_asgn, tab_asgn = res
                        end
                    end
                end
            end
        end
        return arr_asgn, tab_asgn
    end
    # Given that tab[arr][i] has just been set, what have we learned?
    function propagate_fk!(state, ith_arr, arr, src_i)

        # apply heuristics to rule out possibilities from state
        arr_asgn, tab_asgn = state
        fk_val = arr_asgn[arr][src_i]
        println("PROPAGATING arr $(arrs[arr]) #$src_i↦$(fk_val) WITH STATE $arr_asgn\n\t$(join(map(collect,tab_asgn),"\n\t")))")

        # IF WE'VE ASSIGNED OTHER THINGS FOR THIS SRC_I
        # WE HAVE TO CONFIRM THAT THERE EXISTS A COMPATIBLE
        # SRC elem in noncanonical G!!!

        src, tgt = srcs[arr], tgts[arr]
        total_arrows_to_i = [src_ind for (src_ind, val) in enumerate(arr_asgn[arr])
                             if val == fk_val]
        # println("TOTAL ARROWS TO i's value $(total_arrows_to_i)")
        # Does adding a new FK to i push us over the limit for possible targets?

        # these are indices in the original (noncanonical) graph G
        impossible_targets = [ind for (ind, n_pre) in enumerate(n_preimg[arr])
                              if n_pre < length(total_arrows_to_i)]

        for imp in impossible_targets
            deleted = imp in tab_asgn[tgt][fk_val]
            if deleted
                println("\tb/c $(arrs[arr]) sends $(tabs[src])#$src_i↦$(tabs[tgt])#($fk_val), $fk_val in canonical $(tabs[tgt]) cannot refer to $(tabs[tgt])#$imp (from original G)")
                delete!(tab_asgn[tgt][fk_val], imp)
                n = length(tab_asgn[tgt][fk_val])
                if n == 0
                    println("UNSAT")
                    return nothing  # unsatisfiable
                elseif n == 1
                    res = propagate_pk!((arr_asgn, tab_asgn), tgt, fk_val)
                    if res === nothing
                        return nothing
                    else
                        arr_asgn, tab_asgn = res
                    end
                end
            end
        end
        poss_preim = union([g.indices[arr][poss_tgt] for poss_tgt in tab_asgn[tgt][fk_val]]...)
        for src_to_i in total_arrows_to_i # includes src_i, and maybe others
            for src_ind in 1:nparts(g, src)
            # possible preimage values
                if !(src_ind in poss_preim)
                    deleted = src_ind in tab_asgn[src][src_to_i]
                    if deleted
                        println("\tB/c canon. $(tabs[src])#$src_to_i ↦ $tgt#$(tab_asgn[tgt][fk_val]) via $(arrs[arr]), noncanonical preimage of $(poss_preim) means $(tabs[src])#$src_to_i does not correspond to $src_ind")
                        delete!(tab_asgn[src][src_to_i], src_ind)
                        n =length(tab_asgn[src][src_to_i])
                        if n==0
                            println("UNSAT")
                            return nothing
                        elseif n==1
                            res = propagate_pk!((arr_asgn, tab_asgn), src, src_to_i)
                            if res === nothing
                                return nothing
                            else
                                arr_asgn, tab_asgn = res
                            end
                        end
                    end
                end
            end
        end
        return arr_asgn, tab_asgn
    end
    arr_asgn, _ = branch(state)
    new = deepcopy(g)
    for (arr, asgn) in zip(arrs, arr_asgn)
        set_subpart!(new, arr, asgn)
    end
    return new

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