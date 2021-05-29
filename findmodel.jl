include("pathdiagrams.jl");
include("partialmodel.jl");
using Catlab.CategoricalAlgebra
using Base.Iterators: product as prod

#------------------------------------------------
# ENUMERATING ALL MODELS PROJECT
#------------------------------------------------

# Goals:
# [x] Find out how to compute the canonical labeling of a CSet (nauty can't do multi digraphs)
# [x] Add impact of cones to model finding
# [ ] Need a data structure for sketches *defined* as colimits
# [ ] Figure out theoretically how the models are related
# [ ] Work out a database representation of all models found
# [ ] take advantage of colimit substructure
#   - i.e. how to get the enumeration for BIG models given the enumeration of smaller models?
#   - can then solve general problem in 2 steps
#   - 1: compute required models for sub-theories
#   - 2: combine and add stuff as necessary
# [ ] Less important: debug initial term model finding algorithm


"""
General plan for enumeration:
1. Enumerate elements of ℕᵏ for an underlying graph with k nodes.
2. For each of these: (c₁, ..., cₖ), create a term model with that many constants

Do the first enumeration by incrementing n_nonzero
    and finding partitions so that ∑(c₁,...) = n_nonzero

In the future, this function will write results to a database
that hashes the FLS as well as the set of constants that generated the model.
"""
function enum(fls::FLSketch, n::Int)::Dict{Tuple,Vector{CSet}}
    res = Dict{Tuple,CSet}()
    n_const = 0 # total number of constants across all sets
    n_v = nv(fls.G)
    while length(res) < n
        n_const += 1
        for n_nonzero in 1:n_v
            # values we'll assign to nodes
            c_parts = partitions(n_const, n_nonzero)
            # Which nodes we'll assign them to
            indices = permutations(1:n_v,n_nonzero)

            for c_part in c_parts
                for index_assign in indices
                    n_const = zeros(n_v)
                    n_const[index_assign] = c_part
                    n_c = tuple(n_const...)
                    if !(n_c in res)
                        res[n_c] =  term_models(flv, n_c)
                    end
                end
            end
        end
    end
end

"""
We expect two paths to be equal in a model. When we run a query,
we get four values back: for each path, we get the penultimate
and final values along that path.

If at any point along the path we hit an unknown value, the
subsequent values are all unknown. However, in the special
case where one path is completely known and the other path is
known for everything except the final value, we can propagate
this information and fill out the last value of the other path.

It's also possible to learn that the two paths are completely known
but end up in different places. This means the model is not sat.

This function takes the four values and updates the model if possible
(a boolean output flags that there was a change) AND if the equality
was known to be satisfied (+1), unknown (0), or unsatisfiable (-1).
"""
function process_query_result!(mod::Model,
                               end_table::Int,
                               pth1::Vector{Int},
                               pth2::Vector{Int},
                               qres::Vector{Int},
                              )::Pair{Int,Bool}
    change = false
    penult1,penult2,last1,last2 = qres
    nullp1, nullp2, null1, null2 = map(==(1),qres)
    pth2_end = isempty(pth2) ? 0 : pth2[end]
    null_pen, null_end = nullp2 || nullp1, null1 || null2
    # println("nullp1 $nullp1, nullp2 $nullp2, null1 $null1, null2 $null2")
    if !null_pen # we can only do stuff if everything is known up to penultimate
        if null_end  # can propagate info or union two unknowns
        union_fk!(mod, end_table,
                  pth1[end],   # the last edge in path 1
                  penult1-1,   # Factor in the NULL dummy val
                  pth2_end,    # last edge in path 2, if any
                  penult2-1)
        change = true
        sat = null1 && null2 ? 0 : 1
        else  # both known, can check for contradiction
            sat = last1 == last2 ? 1 : -1
        end
    else
        sat = 0
    end
    return sat => change
end
"""
Fill out any info we can from diagrams, detect contradiction
"""
function check_diagrams!(mod::Model, comm_data::Set{Pair{Vector{Int}, Vector{Int}}})::Pair{Bool,Bool}
    change = false
    for (pth1, pth2) in comm_data
        cset = to_cset(mod) # update in between paths
        comm_q = paths_to_query(to_graph(mod), pth1, pth2)
        end_table = mod.tgt[pth1[end]]
        for qres in query(cset, comm_q)
            _,p1,p2,l1,l2=qres
            sat, changed = process_query_result!(
                mod, end_table, pth1, pth2, [p1,p2,l1,l2])
            if sat==-1 return false => false end # FAIL
            change = change || changed
        end
    end
    return true => change
end


"""
Look at each limit cone, call process_cone_match!
on each matching instance in the model.

Returns
- whether the model has *all* cones satisfied
- whether the model is unsat
"""
function check_limits(mod::Model,
                       fls::FLSketch
                      )::Bool
    for (_, cone_dia, cone_map) in cone_data(fls)
        cset = to_cset(mod, fls)
        cone_q = diagram_to_query(cone_dia)
        seen = Set()
        for res in query(cset, cone_q)
            apexes = process_cone_match!(mod, res, cone_map)
            if length(apexes) > 1
                return false
            elseif length(apexes)==1
                if res in seen
                    return false
                else
                    push!(res, seen)
                end
            end
        end
    end
    return true
end

function find_models(fls::FLSketch, consts::Vector{Int})#::Vector{Model}
    # INITIALIZE
    res, seen = Model[], Set{UInt64}()
    modl = Model(fls, consts)

    # Initialize commutative diagram data
    comm_qs = comm_paths_D(fls)
    # precompute cone data here???

    function find_models_rec!(mod::Model)
        println("Mod $mod")
        hsh = hash(mod, fls)
        if !(hsh in seen)
            push!(seen, hsh)
            success, _ = check_diagrams!(mod, comm_qs)
            if success && check_limits(mod, fls)
                if is_sat(mod, fls)
                    println("CANON HASH OF $mod")
                    canon_hsh = canonical_hash(to_cset(mod, true))
                    if !(canon_hsh in seen)
                        push!(res, deepcopy(mod))
                        # println("pushed $(length(res))'th model w/ hash $canon_hsh")
                        push!(seen, canon_hsh)
                    end
                    return
                else
                    choose!(mod)
                end
            end
        end
    end

    """
    Take an FK that is not matched to a PK. Resursively
    explore models that have the FK set to all possible
    values of the PK of the target table OR create a fresh
    PK and map to it.
    """
    function choose!(mod::Model)
        for (e, tgt) in enumerate(mod.tgt)
            tgt_pks = mod.pks[tgt]
            for (src_index, considered) in enumerate(mod.considered[e])
                unconsidered = setdiff(tgt_pks, considered)
                if !isempty(unconsidered)
                    new_mod = deepcopy(mod)
                    new_mod.considered[e][src_index] = Set(tgt_pks)
                    for u in unconsidered
                        newer_mod = deepcopy(new_mod)
                        newer_mod.fks[e][src_index] = u
                        # println("SETTING EDGE $e index $src_index to value $u")
                        find_models_rec!(newer_mod)
                    end
                end
            end
        end
    end

    find_models_rec!(modl)
    return res
end
