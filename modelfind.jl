using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Base.Iterators: product as cartprod
using Catlab.CategoricalAlgebra.FinSets: preimage
include("sketchgat.jl");

"""
Assume one diagram per vertex in G (first index is the start of paths)
Assume at most one cone per vertex in G (last index is the apex)
"""
struct FLS{CD}
    G::CSet{CD}  # a Graph, arrows are "operations"
    D::Vector{T} # diagrams i.e. morphisms to G.
    C::Vector{T} # apex + edges in G from apex
    function FLS(G::CSet{CD},D::Vector{T},C::Vector{T}) where {CD}
      for (i, tt) in enumerate(D)
        @assert codom(tt) == G
        @assert is_natural(tt)
        @assert nv(dom(tt))==0 || tt[:V](1) == i
      end
      for tt in C
        @assert codom(tt) == G
        @assert topological_sort(dom(tt))[1] == nv(dom(tt)) # apex is last
        @assert is_natural(tt)
      end
      return new{CD}(G,D,C)
    end
  end

function xpk(x::Int)::Symbol
    return Symbol("pk$x")
end
function unpk(x::Symbol)::Int
    s = string(x)
    @assert s[:2] == "pk"
    return parse(Int, s[3:end])
end
function xs(x::Int, pk::Bool=false)::Symbol
    return Symbol("x$x"*(pk ? "pk" : ""))
end
function xs(xx::AbstractVector{Int},pk::Bool=false)::Vector{Symbol}
    return [Symbol("x$x",pk) for x in xx]
end
function es(x::Int)::Symbol
    return Symbol("e$x")
end
function es(xx::AbstractVector{Int})::Vector{Symbol}
    [Symbol("e$x") for x in xx]
end

function grph_to_cset(grph::CSet)::CSet
    pres = Presentation(FreeSchema)
    xobs = [Ob(FreeSchema,xs(i)) for i in 1:nv(grph)]
    xpks = [Ob(FreeSchema,xs(i,true)) for i in 1:nv(grph)]
    for i in 1:nv(grph)
        add_generator!(pres, xobs[i])
    end
    for i in 1:nv(grph)
        add_generator!(pres, xpks[i])
        add_generator!(pres, Hom(xpk(i), xobs[i], xpks[i]))
    end
    for (i,(src, tgt)) in enumerate(zip(grph[:src], grph[:tgt]))
        add_generator!(pres, Hom(es(i), xobs[src], xpks[tgt]))
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
    pres = Presentation(FreeSchema)
    n = findfirst(x->occursin("pk", string(x)), collect(tabs)) - 1
    newarrs = collect(arrs)[n+1:end]
    xobs = [Ob(FreeSchema,xs(i)) for i in 1:n]
    for x in xobs
        add_generator!(pres, x)
    end
    for (a, ss, tt) in collect(zip(arrs,src,tgt))[n+1:end]
        add_generator!(pres, Hom(a, xobs[ss], xobs[tt-n]))
    end

    res = CSetType(pres, index=newarrs)()
    order = Vector{Int}[]
    # Copy the data
    for (tabind, tt) in enumerate(tabs[1:n])
        ncomp = nparts(cset, tt)
        add_parts!(res, tt, ncomp)
        push!(order, [findfirst(==(i), cset[xpk(tabind)]) for i in 1:ncomp])
    end
    for (ss, a) in collect(zip(src,arrs))[n+1:end]
        set_subpart!(res, a, cset[a][order[ss]])
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
        x = src_ind in G[:src] ? add_part!(res, xs(tgt_ind)) : 0
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

Returns a diagram
"""
function diagram_data(fls::FLS)::Tuple{CSet,Vector{Int}}
    res = grph_to_cset(fls.G)
    start = Int[]
    for (_, trans) in enumerate(collect(fls.D))
        if nv(dom(trans)) == 0
            push!(start, 0)
        else
            sref, _ = diagram_to_cset!(trans, res)
            push!(start, sref[1])
        end
    end
    freecomplete!(fls.G, res)
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
function cone_data(fls::FLS)::Tuple{Vector{Int}, Vector{CSet}, Vector{Vector{Tuple{Int,Int,Int}}}}
    if isempty(fls.C) return Int[], CSet[], Vector{Tuple{Int,Int,Int}}[] end
    function cone_datum(dia::T)::Tuple{Int, CSet, Vector{Tuple{Int,Int,Int}}}
        apextab = dia[:V](nv(dom(dia)))
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
        legdata = [(dia[:V](tt), dia[:E](e), vind[tt])
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
                    h::Vector{Vector{Int}},
                    apextab::Int,
                    legdata::Vector{Tuple{Int,Int,Int}}
                   )::Vector{Int}
    res = Set(1:nparts(G,apextab)) # anything is possible
    for (ctab, cleg, cind) in collect(legdata)
        cval = h[ctab][cind]
        intersect!(res, G.indices[cleg][G[xpk(ctab)][cval]])
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
                    apextabs::Vector{Int},
                    bases::Vector{CSet},
                    legdatas::Vector{Vector{Tuple{Int,Int,Int}}}
                   )::Tuple{CSet, Bool} where {CD}
    ntab = length(ob(CD))
    cset = deepcopy(cset)
    for (apextab, conebase, legdata) in zip(apextabs,bases, legdatas)
        napex = nparts(cset, apextab)
        apexpk = xpk(apextab)
        baseres = map(getcomps, homomorphisms(conebase, cset))
        if isempty(baseres) && napex != 0 # edge case
            return cset, true
        else
            apexes  = [get_apexes(cset, br, apextab, legdata) for br in baseres]
            dup_apexes, seen_bases = Set{Int}(), Set()
            for (ap, br) in zip(apexes, baseres)
                for a in ap
                    if br in seen_bases
                        push!(dup_apexes, a)
                    end
                    if length(cset.indices[apexpk][cset[apexpk][a]]) == 1
                        push!(seen_bases, br)
                    end
                end
            end

            # fail if there's any element in apextab that can't be an apex for anything
            all_apex = isempty(apexes) ? Set{Int}() : union(apexes...)
            useless_apex = setdiff(Set(1:napex), all_apex)
            apex_pks = Set([cset[apexpk][a] for a in all_apex])
            cset = rem(cset, apextab, useless_apex ∪ dup_apexes)

            dangling_apex = length(apex_pks) < nparts(cset, xs(apextab, true))

            if dangling_apex
                return cset, true
            elseif any(isempty, apexes) # WE HAVE DANGLING BASE!
                allknown = true
                for base in baseres
                    for (ctab, _, cind) in legdata
                        pkfk = xpk(ctab)
                        val = base[ctab][cind]
                        key = cset.indices[pkfk][cset[pkfk][val]]
                        if length(key) > 1
                            allknown = false
                        end
                    end
                end
                if allknown
                    # println("dangling base")
                    return cset, true
                end
            end
        end
    end
    return cset, false
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

    seen, res = Set(), Set()
    init = guess===nothing ? init_grph(fls.G, consts) : guess
    diagram_cset, start = diagram_data(fls)
    apextabs, bases, legdatas = cone_data(fls)

    """
    We can prob do more w/ hres than JUST delete, e.g.
    if 1 path is completely known, infer the other."""
    function search_rec(cset::CSet, depth::Int)::Nothing
        if length(res) == n return nothing end
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

        pks = [ncset.indices[xpk(i)] for i in 1:nv(fls.G)]
        lens = [map(length,x) for x in pks]
        ((nmax, pkmax), tabmax) = findmax(map(x->isempty(x) ? (1,1) : findmax(x), lens))
        if minimum(map(x->isempty(x) ? 1 : minimum(x), lens)) < 1
            if verbose println(dstr*"unsat") end
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

"""Determine which elements to eliminate based on diagram homomorphism result data"""
function elim(cset::CSet, start::Vector{Int}, results::Vector{Vector{Vector{Int64}}})::Vector{Set{Int}}
    res = Dict{Symbol, Vector{Int}}()
    keep = [i == 0 ? Set(1:nparts(cset, tab)) : Set([res[tab][i] for res in results])
            for (tab, i) in enumerate(start)]
    return [setdiff(Set(1:nparts(cset, tab)), k) for (tab,k) in enumerate(keep)]
end

"""
Remove elements from tables - does not change any fk indices
so is only valid for tables which have no arrows to them
OR removing the LAST indices of a table
"""
function rem(orig::CSet, rem::Vector{Set{Int}})::CSet
    res = deepcopy(orig)
    for (comp, reminds) in enumerate(rem)
        # println("remove comp$comp reminds $reminds")
        rem_parts!(res, xs(comp), sort(collect(reminds)))
    end
    return res
end
"""Single table version of `rem`"""
function rem(orig::CSet, tab::Int, rem::Set{Int})::CSet
    res = deepcopy(orig)
    rem_parts!(res, xs(tab), sort(collect(rem)))
    return res
end


"""Eliminate options from a model CSet by choosing a particular
FK combination for a specified PK."""
function choose(orig::CSet{CD}, tab::Int, pk::Int, choice::Int)::Tuple{CSet{CD}, NamedTuple} where {CD}
    pks = orig.indices[xpk(tab)][pk]
    chosen = orig.tables[tab][pks[choice]]
    @assert 0 < choice <= length(pks)
    delinds = Set([p for (i, p) in enumerate(pks) if i!= choice])
    return rem(orig, tab, delinds), chosen
end

"""Extract the mapping data of a CSet CSetTransformation"""
function getcomps(x::CSetTransformation)::Vector{Vector{Int}}
    return [collect(v.func) for v in x.components]
end

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



