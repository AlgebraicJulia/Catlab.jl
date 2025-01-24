module VMHomSearch
export VMSearch, compile_hom_search

using StructEquality, Random
using MLStyle: @match, @data

using ACSets

using ...ACSetTransformations
using ..HomSearch
import ..HomSearch: homomorphisms


""" Find attributed ``C``-set homomorphisms using a virtual machine.
This algorithm compiles the backtracking search algorithm into a flat sequence 
of instructions for faster execution.
"""
struct VMSearch <: ACSetHomomorphismAlgorithm end

function homomorphisms(X::ACSet, Y::ACSet, ::VMSearch; prog=nothing)
  prog = isnothing(prog) ? compile_hom_search(X) : prog
  find_all(prog, X, Y)
end

struct Reg
  idx::Int
end

Base.show(io::IO, r::Reg) = print(io, "[$(r.idx)]")

@data SearchInst begin
  # Iterate through all the rows of a table

  Loop(x::Symbol, reg::Reg)

  # Load a subpart into memory
  Load(from::Reg, subpart::Symbol, into::Reg)

  # Compare two registers for equality, backtrack if they aren't equal
  Compare(r1::Reg, r2::Reg)
end

Base.show(io::IO, l::Loop) = print(io, "LOOP $(l.x)#$(l.reg)")
Base.show(io::IO, l::Load) = print(io, "LOAD $(l.subpart): $(l.from)->$(l.into)")
Base.show(io::IO, l::Compare) = print(io, "COMPARE $(l.r1) ? $(l.r2)")

struct Machine
  registers::Vector{Int}
end

Base.getindex(m::Machine, r::Reg) = m.registers[r.idx]
Base.setindex!(m::Machine, i::Int, r::Reg) = (m.registers[r.idx] = i)

@struct_hash_equal struct NamedPart
  ob::Symbol
  idx::Int
end

struct Program
  next_reg::Ref{Int}
  instructions::Vector{SearchInst}
  lookup::Dict{NamedPart, Reg}
end

function Base.show(io::IO, p::Program)
  for (i, ins) in enumerate(p.instructions)
    print(io, "$i: ")
    println(io, ins)
  end
end

function interpret_search!(m::Machine, prog::Program, a::ACSet, pc::Int, cb::Function)
  if pc > length(prog.instructions)
    cb(m.registers)
  else
    @match prog.instructions[pc] begin
      Loop(x, reg) =>
        for i in parts(a, x)
          m[reg] = i
          interpret_search!(m, prog, a, pc+1, cb)
        end
      Load(from, f, into) => begin
        m[into] = subpart(a, m[from], f)
        interpret_search!(m, prog, a, pc+1, cb)
      end
      Compare(r1, r2) =>
        if m[r1] == m[r2]
          interpret_search!(m, prog, a, pc+1, cb)
        end
    end
  end
end

function find_all(prog::Program, from::ACSet, to::ACSet)
  schema = acset_schema(from)
  homs = NamedTuple{tuple(objects(schema)...), Tuple{[Vector{Int} for _ in objects(schema)]...}}[]
  cb = push_callback(from, homs, prog)
  interpret_search!(Machine(zeros(Int, prog.next_reg[])), prog, to, 1, cb)
  homs
end

function nextreg!(p::Program)
  r = Reg(p.next_reg[])
  p.next_reg[] += 1
  r
end

"""
ordering strategies: 
 - neighbor - order by # of neighbors
 - connected - order by neighbors but prioritize connected components
 - random
"""
function compile_hom_search(X::ACSet, order=nothing; strat=:neighbor)
  S = acset_schema(X)
  if isnothing(order)
    order, queue, seen = Tuple{Symbol,Int}[], Int[], Set{Int}()
    all_parts = vcat([[(o,p) for p in parts(X,o)] for o in ob(S)]...)
    all_d = Dict(p=>i for (i,p) in enumerate(all_parts))
    neighbors = map(all_parts) do (o,p)
      ns = Int[] # indices of neighboring parts
      for (f, _, b) in homs(S; from=o)
        push!(ns, all_d[(b, X[p,f])])
      end
      for (f, a, _) in homs(S; to=o)
        if a != o 
          for ip in incident(X, p, f)
            push!(ns, all_d[(a, ip)])
          end
        end
      end
      ns
    end
    # order neighbor vectors by which ones have the most neighbors
    ordered_neighbors = [sort(ns; by=i->length(neighbors[i])) for ns in neighbors]
    # order parts by same metric
    n_ord = sort(1:length(all_parts), by=i->length(neighbors[i]))
    if strat == :neighbor
      order = all_parts[n_ord] |> reverse
    elseif strat == :random 
      order = shuffle(all_parts)
    elseif strat == :connected
      while !(isempty(n_ord) && isempty(queue))
        if isempty(queue)
          nxt = pop!(n_ord)
          if nxt ∉ seen 
            queue = [nxt]
          end
        else
          curr = pop!(queue)
          push!(order, all_parts[curr]); push!(seen, curr)
          append!(queue, filter(i-> i ∉ seen && i ∉ queue, ordered_neighbors[curr]))
        end
      end
    else 
      error("Unknown order strategy: $strat")
    end
  end
  compile_hom_search(X, [NamedPart(ob, i) for (ob, i) in order])
end

function push_callback(a::ACSet, homs::Vector{T}, prog::Program) where {T<:NamedTuple}
  schema = acset_schema(a)
  function cb(regs::Vector{Int})
    hom = T([zeros(Int, nparts(a, ob)) for ob in objects(schema)])
    for (k,v) in prog.lookup
      hom[k.ob][k.idx] = regs[v.idx]
    end
    push!(homs, hom)
  end
end

allparts(a::ACSet) = Set([NamedPart(ob, i) for ob in objects(acset_schema(a)) for i in parts(a, ob)])

function compile_hom_search(a::ACSet, order::Vector{NamedPart})
  @assert allparts(a) == Set(order)
  schema = acset_schema(a)
  prog = Program(Ref(1), SearchInst[], Dict{NamedPart, Reg}())
  # validate 
  for o in ob(schema) 
    parts = [p.idx for p in order if p.ob == o]
    isperm(parts) && length(parts) == nparts(a, o) || error("Bad part $o $parts")
  end
  for p in order
    if p ∈ keys(prog.lookup)
      continue
    end
    p_reg = nextreg!(prog)
    prog.lookup[p] = p_reg
    push!(prog.instructions, Loop(p.ob, p_reg))
    to_process = [p]
    while !isempty(to_process)
      next = pop!(to_process)
      next_reg = prog.lookup[next]
      for (f, _, d) in homs(schema; from=next.ob)
        r = nextreg!(prog)
        push!(prog.instructions, Load(next_reg, f, r))
        q = NamedPart(d, a[next.idx, f])
        if q ∈ keys(prog.lookup)
          push!(prog.instructions, Compare(prog.lookup[q], r))
        else
          prog.lookup[q] = r
          push!(to_process, q)
        end
      end
    end
  end

  prog
end

end # module