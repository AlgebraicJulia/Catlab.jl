using Catlab.CategoricalAlgebra.CSets
using Catlab.Theories
#------------------------------------------------
# automorphisms
#------------------------------------------------

"""
want to compute these for CSets
    https://ncatlab.org/nlab/show/core-natural+transformation
"""

CDict = Dict{Symbol, Vector{Int}}

function maxx(x::Vector{Int})::Int
    return isempty(x) ? 0 : maximum(x)
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
    isos = sort([apply_automorphism(g, Dict(a)) for a in autos(g)], by=string)
    return isempty(isos) ? g : isos[1]
end

function canonical_hash(g::CSet)::UInt64
    return hash(string(canonical_iso(g)))
end


"""
In theory this could be extended to add extra automorphism-invariant
properties in the output. Right now, we just compute the following pair
for each element of each component:
- number of incident edges from each arrow (from each color)
- the color pointed to by each outgoing edge
"""
CData = Dict{Symbol, Vector{Tuple{Vector{Vector{Int}}, Vector{Int}}}}

function compute_color_data(g::CSet{CD}, prev_color::CDict)::CData where {CD}
    tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
    ntab = eachindex(tabs)
    res = CData()
    a_in  = [[a_ind for (a_ind, t_ind) in enumerate(tgts) if t_ind==i] for i in ntab]
    a_out = [[a_ind for (a_ind, s_ind) in enumerate(srcs) if s_ind==i] for i in ntab]

    for (tgt_ind, tgt) in enumerate(tabs)
        #println("TGT = $tgt")
        subres = Vector{Vector{Int}}[]
        for arr_ind in a_in[tgt_ind]
            #println("ARR = $(arrs[arr_ind])")
            src_ind = srcs[arr_ind]
            src = tabs[src_ind]
            prev_color_src = prev_color[src]
            n_color_src = maxx(prev_color_src)
            preimg = g.indices[arrs[arr_ind]]
            subsubres = Vector{Int}[]
            #println("prev_color_src $prev_color_src\npreimg $preimg \nntgt $(nparts(g, tgt))")
            for tgt_elem in 1:nparts(g, tgt)
                precolor_elem = prev_color_src[preimg[tgt_elem]]
                n_precolor = [count(==(x), precolor_elem) for x in 1:n_color_src]
                push!(subsubres, n_precolor)
            end
            push!(subres, subsubres)
        end
        outgoing_arrows = a_out[tgt_ind]
        out_subres = Vector{Int}[prev_color[tabs[tgts[og]]][g[arrs[og]]] for og in outgoing_arrows]
        res[tgt] = [([ssr[i] for ssr in subres],
                     [osr[i] for osr in out_subres])
                    for i in 1:nparts(g,tgt)]
    end
    return res
end

function invert_perm(x::CDict)::CDict
    function invert_comp(xs::Vector{Int})::Vector{Int}
        return [findfirst(==(v), xs) for v in eachindex(xs)]
    end
    return Dict([k=>invert_comp(v) for (k, v) in collect(x)])
end
"""
Compose permutations (something like this will be useful for automorphism pruning)
"""
function compose_perms(x::CDict, y::CDict)::CDict
    function compose_comp(xs::Vector{Int},ys::Vector{Int})::Vector{Int}
        return [ys[xs[i]] for i in eachindex(xs)]
    end
    return Dict([k=>compose_comp(v1,y[k]) for (k, v1) in collect(x)])
end

function permute_color(σ::CDict, x::CDict)::CDict
    function permute_comp(perm::Vector{Int}, xs::Vector{Int})::Vector{Int}
        return [xs[perm[i]] for i in eachindex(xs)]
    end
    return Dict([k=>permute_comp(σ[k],v) for (k,v) in collect(x)])
end

"""
Iterative color refinement based on the number (and identity) of
incoming and outgoing arrows.
"""
function crefine_iter(g::CSet{CD};
                      init_color::Union{Nothing,CDict}=nothing
                     )::CDict where {CD}
    new_color = (init_color === nothing
                    ? CDict([k => ones(Int, nparts(g, k)) for k in ob(CD)])
                    : init_color)
    prev_n, curr_n, iter = 0, 1, 0
    while prev_n != curr_n
        iter += 1
        prev_color = new_color
        # All that matters about newdata's type is that it is hashable
        newdata = compute_color_data(g, prev_color)
        new_datahash = Dict([k=>map(hash, zip(prev_color[k],v))
                             for (k, v) in collect(newdata)])
        hashes = Dict([k=>sort(collect(Set(v)))
                       for (k,v) in new_datahash])
        new_color = CDict([k=>[findfirst(==(new_datahash[k][i]),hashes[k])
                              for i in 1:nparts(g,k)]
                              for (k,v) in new_datahash])
        prev_n = sum(map(maxx, values(prev_color)))
        curr_n = sum(map(maxx, values(new_color)))
    end
    return new_color
end

function common(v1::Vector{T}, v2::Vector{T})::Int where {T}
    for (i, (x, y)) in enumerate(zip(v1, v2))
        if x != y
            return i-1
        end
    end
    return i
end
"""
DFS tree of colorings with edges being choices in how to break symmetry
Goal is to acquire all leaf nodes.

Note, there is another use of automorphisms not yet implemented:
 - Automorphisms discovered during the search can also be used to prune the search tree in another way. Let d be a node being re-visited by the depth-first search. Let Γ be the group generated by the automorphisms discovered thus far, and let Φ be the subgroup of Γ that fixes d. Suppose that b and c are children of d where some element of Φ maps b to c. If T(G,b) has already been examined, then, as above, there is no need to examine T(G,c). Hence T(G,c) can be pruned from the tree8.
"""
function search_tree(g::CSet{CD},
                     coloring::CDict,
                     split_seq::Vector{Int},
                     tree::Dict{Vector{Int},CDict},
                     perms::Set{Vector{Int}},
                     skip::Set{Vector{Int}}
                    )::Vector{CDict} where {CD}
    tree[split_seq] = coloring
    # To reduce branching factor, split on the SMALLEST nontrivial partition
    colors_by_size = []
    for (k, v) in coloring
        for color in 1:maxx(v)
            n_c = count(==(color), v)
            if n_c > 1
                push!(colors_by_size, n_c => (k, color))
            end
        end
    end

    if isempty(colors_by_size) # LEAF
        # Construct automorphisms between leaves
        tau_inv = invert_perm(coloring)
        for p in perms
            pii = tree[p]
            auto = compose_perms(pii,tau_inv)
            # want to find a,b,c in Fig 4
            i = common(p, split_seq)
            a = tree[p[1:i]]
            if permute_color(auto, a) == a
                b = tree[p[1:i+1]]
                c_location = split_seq[1:i+1]
                c = tree[c_location]
                if permute_color(auto, b) == c
                    push!(skip, c_location)
                end
            end

        end
        push!(perms, split_seq)

    else
        sort!(colors_by_size)
        split_tab, split_color = colors_by_size[1][2]
        colors = coloring[split_tab]
        split_inds = findall(==(split_color), colors)
        for split_ind in split_inds
            if split_seq in skip
                # println("WE SKIPPED $coloring")
            else
                new_coloring = deepcopy(coloring)
                new_seq = vcat(split_seq, [split_ind])
                new_coloring[split_tab][split_ind] = maxx(colors) + 1
                refined = crefine_iter(g; init_color=new_coloring)
                search_tree(g, refined, new_seq, tree, perms, skip)
            end
        end
    end

    return [tree[p] for p in perms]
end

function autos(g::CSet)::Vector{CDict}
    return search_tree(g, crefine_iter(g), Int[],
                       Dict{Vector{Int},CDict}(), Set{Vector{Int}}(), Set{Vector{Int}}())
end

# Brute force find all automorphisms
# function brute(g::CSet)::Set{CDict}
#     tabs, arrs, srcs, tgts = (typeof(g).parameters[1]).parameters
#     ntab = length(tabs)
#     # uncomment to verify brute is not the cause of bottleneck
#     return Set([Dict([t=>collect(1:(nparts(g,t))) for t in tabs])])
#     srcarrs = [[e for (e,s) in enumerate(srcs) if s==i] for i in 1:ntab]
#     function test_combo(comb)::Bool
#         for src in 1:ntab
#             #println("src $src ($(tabs[src]))")
#             srcperm = comb[src]
#             for arr in srcarrs[src]
#                 #println("arr $arr ($(arrs[arr]))")
#                 mapping = g[arrs[arr]]
#                 tgtperm = comb[tgts[arr]]
#                 for i in 1:nparts(g, src)
#                     #println("$i mapping $mapping, srcperm $srcperm tgtperm $tgtperm")
#                     if mapping[srcperm[i]] != tgtperm[mapping[i]]
#                         return false
#                     end
#                 end
#             end
#         end
#         return true
#     end
#     res = Set{CDict}()
#     perms = [collect(permutations(1:nparts(g,s))) for s in tabs]
#     for combo in Iterators.product(perms...)
#         if test_combo(combo)
#             push!(res, Dict(zip(tabs,combo)))
#         end
#     end
#     return res
# end

# """Try to directly find a canonical graph by iterating all
# combinations in order, stopping when an iso is found"""
# function direct_canon(g::CSet{CD})::CSet where {CD}
#     tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
#     src_arrs = [[a_ind for (a_ind, src_tab) in enumerate(srcs) if src_tab==tab] for tab in eachindex(tabs)]
#     # the state is the automorphism from the minimal (lexigraphic) automorph
#     # to the particular g that is used
#     # the first term is the data for the FKs which gets ordered.
#     fk_poss = []
#     for src_arrs_t in src_arrs
#         tab_fk_poss = []
#         for i in 1:length(src_arrs_t)
#             push!(tab_fk_poss, hcat([g[fk] for fk in arrs[1:i]]...))
#         end
#         push!(fk_poss, tab_fk_poss)
#     end
#     state = ([zeros(Int, nparts(g,src)) for src in srcs],
#              [let n=nparts(g,t); [Set{Int}(1:n) for _ in 1:n] end for t in 1:length(tabs)],
#              fk_poss) #

#     n_preimg = [map(length,g.indices[a]) for a in arrs]

#     function branch(state)
#         arr_asgn, tabasgn, fk_poss = state
#         println("BRANCHING WITH STATE $arr_asgn\n\t$(join(map(collect,tabasgn),"\n\t"))")
#         #@assert arr_asgn[2][4] == 0 || (arr_asgn[1][3], arr_asgn[2][3]) != (2,1)
#         for (tab_ind, _) in enumerate(tabs)
#             for (ith_arr, arr) in enumerate(src_arrs[tab_ind])
#                 src,tgt = srcs[arr],tgts[arr]
#                 for i in 1:nparts(g,src)
#                     if arr_asgn[arr][i] == 0
#                         for next_ind in 1:nparts(g,tgt)
#                             println("TRYING IND W/ TAB ASGN \n\t$(join(map(collect,tabasgn),"\n\t"))")
#                             new_asgn = deepcopy(arr_asgn)
#                             new_asgn[arr][i]=next_ind
#                             ta = deepcopy(tabasgn)
#                             res = propagate_fk!((new_asgn, ta, fk_poss), ith_arr, arr, i)
#                             if !(res===nothing)
#                                 return branch(res)
#                             end
#                         end
#                         @assert false
#                     end
#                 end
#             end
#         end
#         return state
#     end
#     function propagate_pk!(state, tab, tab_i)
#         arr_asgn, tabb_asgn, fk_poss = state
#         noncanonical_index, = tabb_asgn[tab][tab_i]
#         println("ENTERING PROPAGATE PK (just discovered $(tabs[tab])#$tab_i ↦ $noncanonical_index) \n\twith tabb_asgn\n\t\t$(join(map(collect,tabb_asgn),"\n\t\t"))")
#         for (tab_ind, tab_poss) in enumerate(tabb_asgn[tab])
#             if tab_ind!=tab_i
#                 deleted = noncanonical_index in tab_poss
#                 if deleted
#                     println("\tb/c $(tabs[tab])#($tab_i) is fixed in the canonical graph to be value $noncanonical_index, $tab#$tab_ind in the canonical graph cannot be $noncanonical_index")
#                     delete!(tab_poss, noncanonical_index)
#                     n = length(tab_poss)
#                     if n == 0
#                         println("UNSAT")
#                         return nothing
#                     elseif n == 1
#                         res = propagate_pk!((arr_asgn, tabb_asgn, fk_poss), tab, tab_ind)
#                         if res === nothing
#                             return nothing
#                         else
#                             arr_asgn, tabb_asgn, fk_poss = res
#                         end
#                     end
#                 end
#             end
#         end
#         return arr_asgn, tabb_asgn, fk_poss
#     end
#     # Given that tab[arr][i] has just been set, what have we learned?
#     function propagate_fk!(state, ith_arr, arr, src_i)

#         # apply heuristics to rule out possibilities from state
#         arr_asgn, tab_asgn, fk_poss = state
#         fk_val = arr_asgn[arr][src_i]
#         println("PROPAGATING arr $(arrs[arr]) #$src_i↦$(fk_val) WITH STATE $arr_asgn\n\t$(join(map(collect,tab_asgn),"\n\t")))")

#         # IF WE'VE ASSIGNED OTHER THINGS FOR THIS SRC_I
#         # WE HAVE TO CONFIRM THAT THERE EXISTS A COMPATIBLE
#         # SRC elem in noncanonical G!!!
#         src, tgt = srcs[arr], tgts[arr]

#         fk_vals = [arr_asgn[srcarr][src_i] for srcarr in src_arrs[src][1:ith_arr]]
#         println("FKVALS")

#         poss_row = false
#         for row in fk_poss[src][ith_arr]
#             this_row = true
#             println("\t\tTesting fkvals $fk_vals vs row $row and poss vals $([tab_asgn[tgt][fkv] for fkv in fk_vals])")
#             for (fk_val,noncanon_fk) in zip(fk_vals,row)
#                 if !(noncanon_fk in tab_asgn[tgt][fk_val])
#                     println("\t\t\tfails")
#                     this_row = false
#                 end
#             end
#             poss_row = poss_row || this_row
#         end
#         println("tab_asgn post poss row check $tab_asgn")
#         if !poss_row
#             println("NO POSSIBLE FK VALS")
#             return nothing
#         end

#         total_arrows_to_i = [src_ind for (src_ind, val) in enumerate(arr_asgn[arr])
#                              if val == fk_val]
#         # println("TOTAL ARROWS TO i's value $(total_arrows_to_i)")
#         # Does adding a new FK to i push us over the limit for possible targets?

#         # these are indices in the original (noncanonical) graph G
#         impossible_targets = [ind for (ind, n_pre) in enumerate(n_preimg[arr])
#                               if n_pre < length(total_arrows_to_i)]

#         for imp in impossible_targets
#             deleted = imp in tab_asgn[tgt][fk_val]
#             if deleted
#                 println("\tb/c $(arrs[arr]) sends $(tabs[src])#$src_i↦$(tabs[tgt])#($fk_val), $fk_val in canonical $(tabs[tgt]) cannot refer to $(tabs[tgt])#$imp (from original G)")
#                 delete!(tab_asgn[tgt][fk_val], imp)
#                 n = length(tab_asgn[tgt][fk_val])
#                 if n == 0
#                     println("UNSAT")
#                     return nothing  # unsatisfiable
#                 elseif n == 1
#                     res = propagate_pk!((arr_asgn, tab_asgn, fk_poss), tgt, fk_val)
#                     if res === nothing
#                         return nothing
#                     else
#                         arr_asgn, tab_asgn, fk_poss = res
#                     end
#                 end
#             end
#         end
#         poss_preim = union([g.indices[arr][poss_tgt] for poss_tgt in tab_asgn[tgt][fk_val]]...)
#         for src_to_i in total_arrows_to_i # includes src_i, and maybe others
#             for src_ind in 1:nparts(g, src)
#             # possible preimage values
#                 if !(src_ind in poss_preim)
#                     deleted = src_ind in tab_asgn[src][src_to_i]
#                     if deleted
#                         println("\tB/c canon. $(tabs[src])#$src_to_i ↦ $tgt#$(tab_asgn[tgt][fk_val]) via $(arrs[arr]), noncanonical preimage of $(poss_preim) means $(tabs[src])#$src_to_i does not correspond to $src_ind")
#                         delete!(tab_asgn[src][src_to_i], src_ind)
#                         n =length(tab_asgn[src][src_to_i])
#                         if n==0
#                             println("UNSAT")
#                             return nothing
#                         elseif n==1
#                             res = propagate_pk!((arr_asgn, tab_asgn, fk_poss), src, src_to_i)
#                             if res === nothing
#                                 return nothing
#                             else
#                                 arr_asgn, tab_asgn, fk_poss = res
#                             end
#                         end
#                     end
#                 end
#             end
#         end
#         return arr_asgn, tab_asgn, fk_poss
#     end
#     arr_asgn, tab_asgn, _ = branch(state)
#     println("FINISHING WITH TAB ASGN $tab_asgn")
#     new = deepcopy(g)
#     for (arr, asgn) in zip(arrs, arr_asgn)
#         set_subpart!(new, arr, asgn)
#     end
#     return new

# end

# """
# Make union-find data structure with elements for each cell (N*(FK+1))
# But collapse to groups using the FK structure of the noncanonical graph
# Map each group to a set of possibilities (1-Ntab) and use this as the
# state. Iteratively attempt to find the lexicographic minimum solution.
# """
# function dc2(g::CSet{CD})::CSet where {CD}
#     tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
#     freevar = []
#     for (src, tgt) in zip(srcs,tgts)
#         append!(freevar,[Set(1:nparts(g, tgt)) for _ in 1:nparts(g,src)])
#     end
#     tabvar, t_offset = [], []
#     for t in tabs
#         push!(t_offset, length(tabvar))
#         append!(tabvar,[Set(1:nparts(g, t)) for _ in 1:nparts(g,t)])
#     end
#     # enforcing equations
#     function enforce_pk_unique(tvars)
#         for t in tabs

#         end
#     end

# end


    #""Compute all automorphisms of a CSet"""
    # function autos(g::CSet) :: Set{CDict}
    #     res = Set{CDict}()
    #     seen = Set{CDict}()
    #     # Initial coloring - everything is 1
    #     cs = Dict([comp=>ones(Int, nparts(g, comp))
    #                for comp in keys(g.tables)])
    #     branch!(g, cs, 1, res, seen)
    #     @assert Dict(:x1=>[1,3,2]) in res
    #     return res
    # end

    # """Take a random color that has multiple nodes and split on it"""
    # function branch!(g::CSet, cs::CDict, depth::Int, res::Set{CDict}, seen::Set{CDict})
    #     println("\n$depth BRANCHING $cs\nseen $([x[:x1] for x in seen])\n")
    #     comps = collect(keys(g.tables))
    #     change = false
    #     for comp in comps  # take a random component
    #         if length(cs[comp]) != length(Set(cs[comp])) # check if it has a color w/ more than one element
    #             max_color = maximum(cs[comp])
    #             color_set = [Set() for _ in 1:max_color]
    #             for (ind, color) in enumerate(cs[comp])
    #                 push!(color_set[color],ind)
    #             end
    #             change=true
    #             for indices in filter(x->length(x)>1,color_set)
    #                 for index in indices
    #                     updated_cs = update_colors(g, deepcopy(cs), comp, index) # result of split
    #                     if !(updated_cs in seen) # result is new
    #                         push!(seen, updated_cs)
    #                         branch!(g, updated_cs, depth+1, res, seen)
    #                     end
    #                 end
    #             end
    #         end
    #     end
    #     if !change
    #         push!(res, cs)
    #     end
    # end

    # """
    # Assign NON-ARBITRARILY ORDERED colors to elements of each component

    # g has an order on its arrows. So for each object x we can consider the tuple
    # (#a_1, #a_2, ...) of arrows that are indicent on x.

    # """
    # function refine_color(g::CSet{CD}, cs::CDict, arrow_ind::Int)::Pair{CDict, Bool} where {CD}
    #     comps, arr, src, tgt = ob(CD), hom(CD), dom(CD), codom(CD)
    #     arrow = arr[arrow_ind]
    #     source, target = [comps[x[arrow_ind]] for x in [src, tgt]]
    #     change = false
    #     target_max_color = maximum(cs[target])
    #     source_max_color = maximum(cs[source])
    #     # partition source table by # of each color that is touched through arrow
    #     counts = [zeros(Int, target_max_color) for _ in 1:nparts(g,source)]
    #     for (color, preimage) in zip(cs[target], g.indices[arrow])
    #         for elem in preimage
    #             # println("$counts $elem $color")
    #             counts[elem][color] += 1
    #         end
    #     end
    #     # condense [col1=2, col2=4,col3=0,...] info into a single value
    #     hshs = map(hash, counts)

    #     # Group the elements of the source table by color
    #     source_parts = [Set{Int}() for _ in 1:source_max_color]
    #     for (source_elem, color) in enumerate(cs[source])
    #         push!(source_parts[color], source_elem)
    #     end

    #     # For each color in the source, we might discover that we
    #     # need more colors. `color_offset` remembers how many colors
    #     # we've added as we iterate through all source colors
    #     color_offset = 1
    #     # Look at the colors that could potentially have a conflict
    #     for part in filter(x->length(x)>1, source_parts)
    #         # get the arrow-color-profile of each source elem of this color
    #         subparts = Dict()
    #         for source_elem in part
    #             hsh = hshs[source_elem]
    #             if haskey(subparts, hsh)
    #                 push!(subparts[hsh], source_elem)
    #             else
    #                 subparts[hsh] = Set([source_elem])
    #             end
    #         end

    #         for source_elems in collect(values(subparts))[2:end] # first partition keeps label
    #             for source_elem in source_elems
    #                 cs[source][source_elem] = source_max_color + color_offset
    #             end
    #             color_offset += 1
    #             change = true
    #         end
    #     end
    #     return cs => change
    # end

    # function refine_colors(g::CSet, cs::CDict)::CDict
    #     n_arrow = length(typeof(g).parameters[1].parameters[2])
    #     change = true
    #     n=0
    #     while change
    #         change = false
    #         for i in 1:n_arrow
    #             cs, changed = refine_color(g, cs, i)
    #             change = change || changed
    #         end
    #         n+=1
    #     end
    #     # println("refined in $n iterations")
    #     return cs
    # end

    # """Differentiate elements by how many nodes of each color they touch"""
    # function update_colors(g::CSet, cs::CDict, tbl::Symbol, val::Int)::CDict
    #     # println("UPDATING tbl $tbl #$val - coloring is $cs")
    #     cs[tbl][val] = maximum(cs[tbl]) + 1
    #     return refine_colors(g, cs)
    # end