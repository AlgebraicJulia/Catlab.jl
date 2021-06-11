

"""
We want to be able to vertically compose FLS
 - define FLS by placing things side-by-side
 - use theory of products (which has 1 model)
   as prerequisite to theory of semigroups
 - two copies of "category" in Functor definition

We want to be able to horizontally compose FLS
 - open graph composition to share variables
   between theories

We want to be able to add restrictions
 - adding more diagrams
 - adding more cones

Assuming we have a strategy to generate all models
(up to isomorphism) of a 'primitive' FLS. How do
we generate all models of the composite?
 - (side note, is there a way to introspect the graph
 of a FLS and deduce a decomposition?)
 - if all we are doing is adding restrictions, do
   we compute without restrictions and then filter?
   (this could be inefficient)
 - if we have variable sharing, do we compute
   seperately and then join models somehow?
   (this could be inefficient)
 - if we have disjoint components, we just take
   the cartesian product of the subsolutions
   (seems optimal)
"""
struct CompositeFLS
end

 function xpk(x::Int)::Symbol
    return Symbol("pk$x")
end

"""Go from pk edge to the table #"""
function unpk(x::Symbol)::Int
    s = string(x)
    @assert s[1:2] == "pk" s
    return parse(Int, s[3:end])
end
"""Go from table # to table name (or name of pk table)"""
function xs(x::Int, pk::Bool=false)::Symbol
    return Symbol("x$x"*(pk ? "pk" : ""))
end
"""Take table name and get table #"""
function unx(x::Symbol)::Int
    s = string(x)
    @assert s[1] == 'x' s
    return parse(Int, s[2:end])
end
"""Take table name and get pk edge"""
function pkedge(x::Symbol)::Symbol
    i = unx(x)
    return Symbol("pk$i")
end
function pktab(x::Symbol)::Symbol
    unx(x)
    return Symbol(string(x)*"pk")
end

function xs(xx::AbstractVector{Int},pk::Bool=false)::Vector{Symbol}
    return [xs(x,pk) for x in xx]
end
function es(x::Int)::Symbol
    return Symbol("e$x")
end
function es(xx::AbstractVector{Int})::Vector{Symbol}
    [Symbol("e$x") for x in xx]
end

function ntabs(_::CSet{CD})::Int where {CD}
    return count(x->occursin("pk", string(x)), ob(CD))
end

function narrs(_::CSet{CD})::Int where {CD}
    return count(x->!occursin("pk", string(x)), hom(CD))
end

function grph_to_cset(grph::CSet)::CSet
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema,xs(i)) for i in 1:nv(grph)]
    xpks = [Ob(FreeSchema,xs(i,true)) for i in 1:nv(grph)]
    for i in 1:nv(grph)
        add_generator!(pres, xobs[i])
    end
    for (i,(src, tgt)) in enumerate(zip(grph[:src], grph[:tgt]))
        add_generator!(pres, Hom(es(i), xobs[src], xpks[tgt]))
    end
    for i in 1:nv(grph)
        add_generator!(pres, xpks[i])
        add_generator!(pres, Hom(xpk(i), xobs[i], xpks[i]))
    end
    alledge = vcat(map(xpk, 1:nv(grph)), es(1:ne(grph)))
    return CSetType(pres, index=alledge)()
end

"""Rename components and arrows"""
function rename(cset    :: CSet{CD},
                onames_ :: Union{Nothing,Vector{Symbol}} = nothing,
                anames_ :: Union{Nothing,Vector{Symbol}} = nothing
               )::CSet where{CD}
    tabs, arrs, src, tgt = ob(CD), hom(CD), dom(CD), codom(CD)
    # Create the new schema
    onames = onames_ === nothing ? collect(tabs) : onames_
    anames = anames_ === nothing ? collect(arrs) : anames_
    @assert length(tabs) == length(onames)
    @assert length(arrs) == length(anames)
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema,o) for o in onames]
    for x in xobs
        add_generator!(pres, x)
    end
    for (i, (ss, tt)) in enumerate(zip(src,tgt))
        add_generator!(pres, Hom(anames[i], xobs[ss], xobs[tt]))
    end
    res = CSetType(pres, index=anames)()
    # Copy the data
    for (oldname, newname) in zip(tabs, onames)
        add_parts!(res, newname, nparts(cset, oldname))
    end
    for (i, (ss, tt)) in enumerate(zip(src,tgt))
        oldname, newname = arrs[i], anames[i]
        set_subpart!(res, newname, cset[oldname])
    end
    return res
end
"""For a fully determined model (exactly one val for each FK)
remove the artificial "pk" tables"""
function clean(cset::CSet{CD},
               oname=nothing,
               aname=nothing
              )::CSet where{ CD}

    tabs, arrs, src, tgt = ob(CD), hom(CD), dom(CD), codom(CD)
    println("CLEANING WITH TABS $tabs\nAND ARRS $arrs")
    n_tab, n_arr = ntabs(cset), narrs(cset)
    n_map = [findfirst(==(xs(i)), tabs) for i in 1:n_tab]
    e_map = [findfirst(==(es(i)), arrs) for i in 1:n_arr]
    # n_map_rev = Dict([s=>(s[(end-1):end] == "pk" ? parse(Int,s[2:end-2]) : parse(Int,s[2:end]))
    #                   for s in map(string,tabs)])
    pres = Presentation(FreeSchema)
    newarrs = es(1:n_arr)
    xobs = [Ob(FreeSchema,xs(i)) for i in 1:n_tab]
    for x in xobs
        add_generator!(pres, x)
    end
    for i in 1:n_arr
        ss, tt = src[i],tgt[i]
        targ = tt - n_tab
        add_generator!(pres, Hom(es(i), xobs[ss], xobs[targ]))
    end

    res = CSetType(pres, index=newarrs)()
    order = Vector{Int}[]
    # Copy the data
    for tabind in 1:n_tab
        ncomp = nparts(cset, xs(tabind))
        add_parts!(res, xs(tabind), ncomp)
        push!(order, [findfirst(==(i), cset[xpk(tabind)]) for i in 1:ncomp])
    end
    for arr_ind in 1:n_arr
        ss = src[arr_ind]
        set_subpart!(res, es(arr_ind), cset[es(arr_ind)][order[ss]])
    end

    return rename(res, oname, aname)
end
"""Adds a diagram to a cset"""
function diagram_to_cset!(trans::CSetTransformation, res::CSet
                         )::Tuple{Vector{Int}, Vector{Int}}
    G, sref, tref = dom(trans), [], []
    # populate parts
    for (src_ind, tgt_ind) in enumerate(collect(trans[:V]))
        # there is no need to create anything more than a PK reference
        # for something that is merely a target
        #x = src_ind in G[:src] ? add_part!(res, xs(tgt_ind)) : 0
        x = add_part!(res, xs(tgt_ind))
        px = add_part!(res, xs(tgt_ind,true))
        push!(sref, x)
        push!(tref, px)
        if x > 0 set_subpart!(res, x, xpk(tgt_ind), px) end
    end
    # populate known edges
    for (e, (src,tgt)) in enumerate(zip(G[:src], G[:tgt]))
        set_subpart!(res, sref[src], es(trans[:E](e)), tref[tgt])
    end
    return sref, tref
end

"""
Asssume FLS has one diagram per component (if any) with the root
being index 1.

Returns a diagram AND information about which nodes correspond
to the starting point.
"""
function diagram_data(fls::FLS;free::Bool=true)::Tuple{CSet,Dict{Symbol, Int}}
    res = grph_to_cset(fls.G)
    start = Dict{Symbol, Int}()
    for trans in fls.D
        sref, _ = diagram_to_cset!(trans, res)
        start[xs(trans.components[:V](1))] = sref[1]
    end
    if free freecomplete!(fls.G, res) end
    return res, start
end

"""freely complete any dangling edges"""
function freecomplete!(schema::CSet, cset::CSet)
    for (e, tgt) in enumerate(schema[:tgt])
        for (src_ind, fkval) in enumerate(cset[es(e)])
            if fkval == 0
                fresh = add_part!(cset, xs(tgt, true))
                set_subpart!(cset, src_ind, es(e), fresh)
            end
        end
    end
end

"""
Legdata is a dictionary of i::Int => (t::Int, e::Int)
where i refers to an index of the base diagram
      t refers to the table (in the main graph) it corresponds to
      e refers to the edge (in the main graph) that connects the apex
Therefore, given a `res` from querying the base diagram, the apex must
  be the unique inhabitant of the intersection of the preimages for
  each edge e (for element `res[i]``)
"""
function cone_data(fls::FLS)::Tuple{Vector{Symbol}, Vector{CSet}, Vector{Vector{Tuple{Symbol,Symbol,Int}}}}
    if isempty(fls.C) return Int[], CSet[], Vector{Tuple{Symbol,Symbol,Int}}[] end
    function cone_datum(dia::T)::Tuple{Symbol, CSet, Vector{Tuple{Symbol,Symbol,Int}}}
        apextab = xs(dia[:V](nv(dom(dia))))
        newdom = deepcopy(dom(dia))
        cone_edges = collect(newdom.indices[:src][nv(newdom)])
        cone_tgts = [newdom[:tgt][e] for e in cone_edges]
        rem_edges!(newdom, cone_edges) # remove all edges from cone
        rem_vertex!(newdom, nv(newdom))

        new_comps = Dict([:V => collect(dia[:V])[1:end-1],
                          :E => [e for (i, e) in enumerate(collect(dia[:E])) if !(i in cone_edges)]])

                          img = CSetTransformation(newdom, codom(dia); new_comps...)
        base = grph_to_cset(fls.G)
        vind, _ = diagram_to_cset!(img, base)
        legdata = [(xs(dia[:V](tt)), es(dia[:E](e)), vind[tt])
                   for (e, tt) in zip(cone_edges, cone_tgts)]
        freecomplete!(codom(dia), base)

        return apextab, base, legdata
    end
    apextabs, bases, legdatas = map(collect, zip(map(cone_datum, fls.C)...))
    return apextabs, bases, legdatas
end

"""
Initialize a model Cset with all possible FK combinations,
starting with the number of elements in each table.
"""
function init_grph(grph::CSet, init::Vector{Int})::CSet
    res = grph_to_cset(grph)
    vals = [Int[] for _ in 1:nv(grph)]
    edges = [Symbol[] for _ in 1:nv(grph)]
    for v in 1:nv(grph)
        e_out = grph.indices[:src][v]
        vals[v] = vcat([init[v]], Int[init[grph[:tgt][e]] for e in e_out])
        edges[v] = vcat([xpk(v)], [es(e) for e in e_out])
        add_parts!(res, xs(v,true), init[v])
        add_parts!(res, xs(v), prod(vals[v]))
    end
    for v in 1:nv(grph)
        for (i,combo) in enumerate(cartprod([1:z for z in vals[v]]...))
            for (e, fkval) in zip(edges[v],combo)
                set_subpart!(res, i, e, fkval)
            end
        end
    end
    return res
end

"""
Given a morphism from the cone diagram to the model, find what are the
possible apexes
"""
function get_apexes(G::CSet,
                    h::Dict{Symbol,Vector{Int}},
                    apextab::Symbol,
                    legdata::Vector{Tuple{Symbol,Symbol,Int}}
                   )::Vector{Int}
    res = Set(1:nparts(G,apextab)) # anything is possible
    #println("G $G")
    for (ctab, cleg, cind) in collect(legdata)
        cpk_edge = pkedge(ctab)
        if cind > 0
            cval = h[ctab][cind]
            #println("ctab $ctab cleg $cleg cind $cind cval $cval ")
            cpk = G[cpk_edge][cval]
            #println("G[xpk(ctab)][cval] $(G[xpk(ctab)][cval]) \n\tcpk $cpk \n\tG.indices[cleg] $(G.indices[cleg])")
            intersect!(res, G.indices[cleg][cpk])
        end
    end
    return collect(res)
end
"""
Return `true` if limit constraints make the cset provably UNsat, `false` otherwise

Our model starts off with all possibilities and whittles them down.
So if we have a cone base, it's only a potential cone. Therefore we should not
instantly fail if we can't find an apex for it (future choices may eliminate the cone)
However, if all elements in the cone have been determined already (only one set of FKs
for the PKs involved) then we can fail.

In the case of having an apex that can't be matched to any cone bases, we can fail
instantly (no further decisions will undo that).

"""
function limitcheck(cset::CSet{CD},
                    apextabs::Vector{Symbol},
                    bases::Vector{CSet},
                    legdatas::Vector{Vector{Tuple{Symbol,Symbol,Int}}}
                   )::Tuple{CSet, Bool} where {CD}
    verbose = false

    cset = deepcopy(cset)
    to_delete = Dict{Symbol, Set{Int}}()
    for (apextab, conebase, legdata) in zip(apextabs,bases, legdatas)
        napex = nparts(cset, apextab)
        apex_pk, apex_pk_edge = pktab(apextab), pkedge(apextab)
        baseres = map(getcomps, homomorphisms(conebase, cset))
        @assert length(baseres) == length(Set(baseres))
        if isempty(baseres)  # edge case
            if napex != 0
                return cset, true
            else
                continue
            end
        else
            apexes  = [get_apexes(cset, br, apextab, legdata) for br in baseres]
            dup_apexes, seen_bases,  = Set{Int}(), Set()
            apex_pks, all_apex = Set(), Set()

            # Look for duplicate apexes
            # If two apex PKs are completely determined, then they should only
            # appear once when iterating through base results (note this assumes
            # base_res has unique values). When we see multiple, we flag all but
            # the first for deletion.
            for (ap, br) in zip(apexes, baseres)
                for a in ap
                    if br in seen_bases
                        push!(dup_apexes, a)
                    end
                    pkval = cset[apex_pk_edge][a]
                    push!(apex_pks, pkval)
                    push!(all_apex, a)
                    if length(cset.indices[apex_pk_edge][pkval]) == 1
                        push!(seen_bases, br)
                    end
                end
            end

            useless_apex = setdiff(Set(1:napex), all_apex)
            delapex = useless_apex ∪ dup_apexes

            # we've flagged rows of the apex table (say, C) to delete
            # but if one of the cone legs is to C itself, then looking
            # up the apex may hit a deleted index.
            self_legs = [leg for (ctab, leg, _) in legdata if ctab == apextab]
            # Iteratively add to delapex until convergence.
            # Delete an apex row if its parent cone has been deleted
            n_delapex = -1
            while n_delapex != length(delapex)
                n_delapex = length(delapex)
                for non_del_apex in setdiff(1:napex, delapex)
                    non_del_pk = cset[apex_pk_edge][non_del_apex]
                    for self_leg in self_legs
                        parents = cset.indices[self_leg][non_del_pk]
                        if all(p->p ∈ delapex, parents)
                            push!(delapex,non_del_apex)
                        end
                    end
                end
            end

            # new_cone_inds = reindex(napex, sort(collect(delapex)))
            to_delete[apextab] = delapex
            dangling_apex = length(apex_pks) < nparts(cset, apex_pk)
            if dangling_apex
                if verbose println("DANGLING APEX") end
                return cset, true
            else
                if any(isempty, apexes) # WE HAVE DANGLING BASE!
                    allknown = true
                    for base in baseres
                        for (ctab, _, cind) in legdata
                            pkfk = pkedge(ctab)
                            val = base[ctab][cind]
                            key = cset.indices[pkfk][cset[pkfk][val]]
                            if length(key) > 1
                                allknown = false
                            end
                        end
                    end
                    if allknown
                        if verbose println("dangling base") end
                        return cset, true
                    end
                end
            end
        end
    end

    return rem(cset, to_delete), false
end

function pklengths(cset::CSet)::Vector{Vector{Int}}
    n = ntabs(cset)
    pks = [cset.indices[xpk(i)] for i in 1:n]
    return [map(length,x) for x in pks]
end

"""
Find `n` models (with cardinality fixed by `consts`)
that match the diagram and limit constraints.
Optionally start with initial guess that has some possibilities removed.
"""
function search(fls::FLS,
                consts::Vector{Int},
                n::Int=-1,
                guess::Union{Nothing,CSet}=nothing;
                verbose=false
               )::Vector{CSet}
    @assert all(x->x>=0, consts)
    @assert length(consts) == nv(fls.G)
    seen, res = Set(), Set()
    init = guess===nothing ? init_grph(fls.G, consts) : guess
    diagram_cset, start = diagram_data(fls)
    apextabs, bases, legdatas = cone_data(fls)

    """
    We can prob do more w/ hres than JUST delete, e.g.
    if 1 path is completely known, infer the other."""
    function search_rec(cset::CSet, depth::Int)::Nothing
        if length(res) == n return nothing end
        # LOOK AT COMMUTATIVE DIAGRAMS
        hres = map(getcomps, homomorphisms(diagram_cset, cset));
        dstr = repeat("\t", depth)
        todelete = elim(cset, start, hres)
        newcset = rem(cset, todelete)
        if newcset != cset
            newhsh = canonical_hash(newcset)
            if newhsh in seen
                return nothing
            else
                push!(seen, newhsh)
            end
        end
        # LOOK AT CONE DIAGRAMS
        ncset, fail = limitcheck(newcset, apextabs, bases, legdatas)
        if newcset != ncset
            newhsh = canonical_hash(ncset)
            if newhsh in seen
                return nothing
            else
                push!(seen, newhsh)
            end
        end

        if fail
            if verbose println(dstr*"limitfail") end
            return nothing
        end


        lens = pklengths(ncset)
        ((nmax, pkmax), tabmax) = findmax(map(x->isempty(x) ? (1,1) : findmax(x), lens))
        if minimum(map(x->isempty(x) ? 1 : minimum(x), lens)) < 1
            if verbose println(dstr*"unsat $lens") end
            return nothing
        elseif nmax == 1
            push!(res, ncset)
        else
            if verbose println(dstr*"SPLITTING ON $(xs(tabmax)) pk$pkmax ($nmax)") end
            for i in 1:nmax # split on the largest FK
                newer_cset, choice = choose(ncset, tabmax, pkmax, i)
                if verbose println(dstr*"CHOICE $i/$nmax = $choice") end
                newhsh = canonical_hash(newer_cset)
                if !(newhsh in seen)
                    push!(seen, newhsh)
                    if verbose println(dstr*"(new split)") end
                    search_rec(newer_cset, depth+1)
    end end end
    return nothing end
    search_rec(init,0)
    return collect(res)
end

function search(fls::FLS, consts::Vector{Int},onames::Vector{Symbol}, anames::Vector{Symbol})
    res = search(fls, consts)
    return [clean(r, onames, anames) for r in res]
end

"""Determine which elements to eliminate based on diagram homomorphism result data"""
function elim(cset::CSet, start::Dict{Symbol, Int}, results::Vector{Dict{Symbol,Vector{Int}}})::Dict{Symbol, Set{Int}}
    n_tab = ntabs(cset)
    if length(results) == 0
        return Dict([tab=>Set(1:nparts(cset, tab)) for tab in xs(1:n_tab)])
    end
    ks, n = keys(start), ntabs(cset)
    keep = [i=>i ∈ ks ? Set([res[i][start[i]] for res in results]) : 1:nparts(cset, i)
            for i in xs(1:n)]
    return Dict([tab=>setdiff(Set(1:nparts(cset, tab)), k) for (tab,k) in collect(keep)])
end

"""
Remove elements from tables - does not change any fk indices
so is only valid for tables which have no arrows to them
OR removing the LAST indices of a table
"""
function rem(orig::CSet, rem::Dict{Symbol, Set{Int}})::CSet
    res = deepcopy(orig)
    for (comp, reminds) in collect(rem)
        rem_parts!(res, comp, sort(collect(reminds)))
    end
    return res
end
"""Single table version of `rem`"""
function rem(orig::CSet, tab::Symbol, rem::Set{Int})::CSet
    res = deepcopy(orig)
    rem_parts!(res, tab, sort(collect(rem)))
    return res
end


"""Eliminate options from a model CSet by choosing a particular
FK combination for a specified PK."""
function choose(orig::CSet{CD}, tab::Int, pk::Int, choice::Int)::Tuple{CSet{CD}, NamedTuple} where {CD}
    pks = orig.indices[xpk(tab)][pk]
    chosen = orig.tables[tab][pks[choice]]
    @assert 0 < choice <= length(pks)
    delinds = Set([p for (i, p) in enumerate(pks) if i!= choice])
    return rem(orig, xs(tab), delinds), chosen
end

"""Extract the mapping data of a CSet CSetTransformation"""
function getcomps(x::CSetTransformation)::Dict{Symbol,Vector{Int}}
    cs = keys(x.components)
    return Dict([c=>collect(v.func) for (c, v) in zip(cs, x.components)])
end



function reindex(n::Int, removed::Vector{Int})::Vector{Int}
    offset, off_counter, o_index = [],0,1
    for i in 1:n
        while o_index <= length(removed) && removed[o_index] < i
            if removed[o_index] < i
            off_counter +=1
            end
            o_index += 1
        end
    push!(offset, off_counter)
    end
    return offset
end

# These functions below are no longer needed but may be useful

"""The image of a CSetTransformation, as a CSet"""
function image(m::CSetTransformation{CD})::CSet{CD} where {CD}
    tabs, arrs, srcs, tgts = ob(CD), hom(CD), dom(CD), codom(CD)
    G = dom(m)
    new = deepcopy(G)
    vals, preim = Dict(), Dict()
    for (c, fun) in zip(keys(m.components), m.components)
        rem_parts!(new, c, 1:nparts(new,c))
        vals[c] = collect(Set(collect(fun)))
        preim[c] = [collect(preimage(fun, v)) for v in vals[c]]
        add_parts!(new, c, length(vals[c]))
    end
    for (a,s_,t_) in zip(arrs, srcs, tgts)
        s, t = tabs[s_], tabs[t_]
        newpart= []
        for (i, v) in enumerate(vals[s])
            pre = preim[s][v]
            newval = m.components[t](G[a][pre[1]])
            new_ind = findfirst(==(newval), vals[t])
            push!(newpart, new_ind)
        end
        set_subpart!(new, a,newpart)
    end
    return new
end


"""Remove cleanly - not needed for the FK values b/c nothing points to them"""
function remove(orig::CSet{CD},rem::Dict{Symbol, Set{Int}})::CSet where {CD}
    tabs, arrs, src, tgt = ob(CD), hom(CD), dom(CD), codom(CD)
    res = deepcopy(orig)
    offsets = Dict{Symbol, Vector{Int}}()
    saved = Dict{Symbol, Vector{Int}}()
    for (tab, reminds) in collect(rem)
        n = nparts(orig, tab)
        rem_parts!(res, tab, 1:n)
        add_parts!(res, tab, n - length(reminds))
        offsets[tab] = reindex(n, sort(collect(reminds)))
        saved[tab] = [i for i in 1:n if !(i in reminds)]
    end
    for (a, s, t) in zip(arrs, src, tgt)
        srcinds = get(saved, tabs[s], 1:nparts(orig,s))
        offs = get(offsets, tabs[t], zeros(Int,nparts(orig, t)))
        new=[val - offs[val] for val in orig[a][srcinds]]
        set_subpart!(res, a, new)
    end
    return res
end

