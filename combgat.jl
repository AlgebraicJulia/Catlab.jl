using Catlab.Theories
using Catlab.CSetDataStructures
using Catlab.CategoricalAlgebra.CSets

using Catlab.Present


"""
Roadmap:

Ring (from Group+CommGroup)
CommGroup (from Group + AbMagma)
Group (from Mon)
Monoid (from SG)
SemiGroup (from Magma)
AbelianMagma (from magma)
Magma (from Set)
Set

[x] Define some of these things "manually"
[ ] Define some using inclusions or pushouts
[ ] Check that results are isomorphic (ignoring Attr)
[ ] Check that a pretheory is a valid theory
[ ] Figure out a way to hash this CSet (i.e. compute isomorphism class)
[ ] Convenience for constructing
[x] Pretty printing
[ ] (Big goal: enumeration of models of a GAT in order of simplicity)
"""

#------------

"""
A pretheory represented as combinatorial object

Currently has attributes for labels to help
interpretability, but they ought be removed.

Some further rules could be imposed to restrain
the number of syntactically valid pretheories, e.g.:
- no two separate introduction rules can refer to the
  same concrete sorts/terms
- Every concrete term/sort must show up in some intro
- axioms must relate at least 2 terms
- no term gets assigned an operation multiple times

"""
@present TheoryGAT(FreeSchema) begin

  # E.g. Ob/Hom
  SortCon::Ob
  # E.g. id/compose
  TermCon::Ob
  # E.g. left-identity, id(A)⋅f
  (Axiom, AxTerm)::Ob
  # E.g. the 2nd arg of Hom constructor,
  # or the 1st arg of id operation
  (SortConArg, TermConArg)::Ob
  # E.g. Hom(A,B), id(A) ⋅ id(A)
  (Sort, Term)::Ob
  # E.g. the 2nd arg of Hom(A,B), the 1st arg of id(A)
  (SortArg, TermArg)::Ob
  # E.g. the outer operator "⋅" of "id(A) ⋅ f"
  # why this is an Ob (instead of a Hom) explained below
  TermOp::Ob

  # Indicate arity of each sort
  # and provide the argument type
  sca_parent::Hom(SortConArg, SortCon)
  sca_sort::Hom(SortConArg,Sort)

  # Indicate arity of each operation
  # provide the canonical argument
  # (i.e. in the declaration)
  tca_parent::Hom(TermConArg, TermCon)
  tca_term::Hom(TermConArg, Term)

  # Given the canonical arguments
  # (with vars interpreted as patterns)
  # what is the resulting sort?
  op_sort::Hom(TermCon, Sort)

  # Connect an applied sort to its args
  # noting which arg of sort constructor is used
  sortarg_sort::Hom(SortArg, Sort)
  sortarg_arg::Hom(SortArg, SortConArg)
  sortarg_val::Hom(SortArg, Term)

  # Connect an application term to its args
  # noting which arg of term constructor is used
  termarg_term::Hom(TermArg, Term)
  termarg_arg::Hom(TermArg, TermConArg)
  termarg_val::Hom(TermArg, Term)

  # Want 0 OR 1 operations associated with a term
  # (0 means variable, 1 means otherwise)
  termop_term::Hom(TermOp, Term)
  termop_op::Hom(TermOp, TermCon)

  # Every concrete sort has exactly one constructor associated
  sortcon::Hom(Sort,SortCon)

  # Every term has a sort (with sort axioms, this becomes dubious)
  termsort::Hom(Term, Sort)

  # Relation between terms and axioms
  at_ax::Hom(AxTerm, Axiom)
  at_term::Hom(AxTerm, Term)

  # Not necessary, just for labelling
  Name::Data
  scname::Attr(SortCon, Name)
  oname::Attr(TermCon, Name)
  sname::Attr(Sort, Name)
  tname::Attr(Term, Name)
  aname::Attr(Axiom, Name)
end;

const Gat = ACSetType(TheoryGAT, index=[
    :at_ax,:at_term, :sortarg_sort, :termop_term,
    :termarg_term, :sca_parent, :tca_parent]){String};

#-------------

cat = @acset Gat begin
    SortCon = 2
    TermCon = 2
    SortConArg = 2
    TermConArg = 3
    Sort = 14
    SortArg = 26
    Term = 24
    TermOp = 8
    TermArg = 14
    Axiom = 2
    AxTerm = 5

    scname = ["Ob", "Hom"]
    oname = ["id", "comp"]

    sca_parent = [2,2]
    sca_sort = [1,1]

    tca_parent      = [1,2, 2]
    tca_term = [1,9,10]

    op_sort = [2, 5]

    sortcon = vcat([1],repeat([2], 13))
    sname = ["Ob",    "HomΓΓ", "HomAB", "HomBC", "HomAC",
             "Homab", "Hombc", "Homcd", "Homac", "Hombd",
             "Homad", "Homαα", "Homββ", "Homαβ"]

    sortarg_sort = [2,2,3,3,4,4,5,5,6,6, 7, 7, 8, 8, 9, 9, 10,10,11,11, 12, 12, 13, 13, 14, 14]
    sortarg_val  = [1,1,2,3,3,4,2,4,5,6, 6, 7, 7, 8, 5, 7, 6, 8, 5, 8,  18, 18, 19, 19, 18, 19]
    sortarg_arg  = repeat([1,2], 13)

    termsort=[1, 1, 1, 1, 1,
              1, 1, 1, 3, 4,
              6, 7, 8, 9, 10,
              11, 11,
              1, 1, 12, 13,
              14, 14, 14]

    tname=["Γ",    "A",   "B",   "C",     "a",
           "b",    "c",   "d",   "f",  "g",
           "p",    "q","r","p.q","q.r",
           "p.(q.r)", "(p.q).r",
           "α",     "β",      "id(α)", "id(β)",
           "f",    "id(α).f", "f.id(β)"]

    termop_op  =  [2, 2, 2, 2, 1, 1, 2, 2]
    termop_term = [14,15,16,17,20,21,23,24]

    termarg_term = [14,14,15,15,16,16,17,17,
                    20,21,23,23,24,24]
    termarg_arg =  [2, 3, 2, 3, 2, 3, 2, 3,
                    1, 1, 2, 3, 2, 3]
    termarg_val =  [11,12,12,13,11,15,14,13,
                    18,19,20,22,22,21]

    at_ax   = [1, 1, 2, 2, 2]
    at_term = [16,17,22,23,24]
    aname=["Associativity", "Unit"]
end;

setgat = @acset Gat begin
    SortCon = 1
    scname = ["G"]
end;

magma = @acset Gat begin
    SortCon = 1
    TermCon = 1
    TermConArg = 2
    Sort = 1
    Term = 2
    scname = ["G"]
    sname = ["G"]
    oname = ["*"]
    tca_parent = [1, 1]
    tca_term = [1, 2]
    op_sort = [1]
    termsort = [1, 1]
    sortcon = [1]
    tname = ["x", "y"]
end;

abel_magma = @acset Gat begin
    SortCon = 1
    TermCon = 1
    TermConArg = 2
    TermOp = 2
    TermArg = 4
    Sort = 1
    Term = 4
    Axiom = 1

    scname = ["G"]
    sname = ["G"]
    oname = ["*"]
    tca_parent = [1, 1]
    tca_term = [1, 2]
    op_sort = [1]
    termsort = [1, 1, 1, 1]
    sortcon = [1]
    tname = ["x", "y", "x*y", "y*x"]
    termop_op =[1, 1]
    termop_term = [3, 4]
    termarg_term = [3,3,4,4]
    termarg_arg = [1, 2, 1, 2]
    termarg_val = [1,2,2,1]
    ax1 = [3]
    ax2 = [4]
    aname = ["symmetry"]
end;

semigroup = @acset Gat begin
    SortCon = 1
    TermCon = 1
    TermConArg = 2
    Sort = 1
    Term = 7
    TermArg = 8
    TermOp = 4
    Axiom = 1
    AxTerm = 2
    scname = ["G"]
    sname = ["G"]
    oname = ["*"]
    tca_parent = [1, 1]
    tca_term = [1, 2]
    op_sort = [1]
    termsort = [1, 1, 1, 1, 1, 1, 1]
    sortcon = [1]
    tname = ["x", "y", "z", "x*y", "y*z", "x*(y*z)", "(x*y)*z"]
    termop_op =[1, 1,1,1]
    termop_term = [4,5,6,7]

    termarg_term = [4,4,5,5,6,6,7,7]
    termarg_arg  = [1,2,1,2,1,2,1,2]
    termarg_val  = [1,2,2,3,1,5,4,3]

    at_ax=[1,1]
    at_term=[6,7]
    aname=["associativity"]
end;

monoid = @acset Gat begin
    SortCon = 1
    TermCon = 2
    TermConArg = 2
    Sort = 1
    Term = 11
    TermArg = 12
    TermOp = 7
    Axiom = 2
    AxTerm = 5
    scname = ["G"]
    sname = ["G"]
    oname = ["*", "e"]
    tca_parent = [1, 1]
    tca_term = [1, 2]
    op_sort = [1, 1]
    termsort = ones(Int, 11)
    sortcon = [1]
    tname = ["x",       "y",       "z", "x*y", "y*z",
             "x*(y*z)", "(x*y)*z", "e()", "a", "a*e",
             "e*a"]
    termop_op =   [1,1,1,1,2,1, 1]
    termop_term = [4,5,6,7,8,10,11]

    termarg_term = [4,4,5,5,6,6,7,7,10,10,11,11]
    termarg_arg  = [1,2,1,2,1,2,1,2,1, 2, 1, 2]
    termarg_val  = [1,2,2,3,1,5,4,3,9, 8, 8, 9]

    at_ax  =[1,1,2,2, 2]
    at_term=[6,7,9,10,11]
    aname=["associativity", "unit"]
end;

#-------------

"""Print term along with type"""
function typedterm(thy::ACSet, term::Int)::String
    return "$(thy[:tname][term]):$(thy[:sname][thy[:termsort][term]])"
end

"""Render a judgment with premises and conclusion"""
function sequent(top::Vector{String}, bottom::Vector{String}, side::String)::String
    topline = join(top, " ")
    bottomline = join(bottom, " = ")
    lt, lb = map(length, [topline, bottomline])
    maxlen = max(lt, lb)
    offt, offb = map(x -> Int(round((maxlen-x)/2)), [lt, lb])
    midline = repeat('-', maxlen) * "  " * side
    return join([repeat(" ", offt) * topline,
                 midline,
                 repeat(" ", offb) * bottomline * "\n"], "\n")
end

"""Given some terms, construct the appropriate context"""
function getctx(thy::ACSet, terms::Vector{Int})::Vector{Int}
    res = []
    terms = deepcopy(terms)
    while !isempty(terms)
        t = pop!(terms)
        if isempty(thy.indices[:termop_term][t])
            if !(t in res)
                push!(res, t)
                ts = thy[:termsort][t]
                tsa = thy.indices[:sortarg_sort][ts]
                tst = thy[:sortarg_val][tsa]
                append!(terms, tst)
            end
        else
            children = thy[:termarg_val][thy.indices[:termarg_term][t]]
            append!(terms, children)
        end
    end
    return reverse(res)
end

subs = ["₁","₂","₃","₄","₅","₆","₇","₈","₉"]

"""Pretty print theory"""
function theory(thy::ACSet)::String
    res = ["Sorts\n-----\n"]
    for srt in 1:length(thy.tables[:SortCon])
        name = thy[:scname][srt]
        args = thy.indices[:sca_parent][srt]
        sorts = thy[:sca_sort][args]
        top = ["x$(subs[i]):$(thy[:sname][s])" for (i, s) in enumerate(sorts)]
        bot = ["$name($(join(["x$(subs[i])" for i in 1:length(sorts)], ",")))"]
        push!(res, sequent(top, bot, name))
    end
    push!(res, "\nOperations\n----------\n")
    for op in 1:length(thy.tables[:TermCon])
        args = thy.indices[:tca_parent][op]
        argvals = thy[:tca_term][args]
        top = [typedterm(thy, t) for t in getctx(thy, argvals)]
        name = thy[:oname][op]
        bot = ["$name($(join(thy[:tname][argvals],","))) : $(thy[:sname][thy[:op_sort][op]])"]
        push!(res, sequent(top, bot, name))
    end
    push!(res,"\nAxioms\n------\n")
    for ax in 1:length(thy.tables[:Axiom])
        terms = [thy[:at_term][axt]
                 for axt in thy.indices[:at_ax][ax]]
        top = [typedterm(thy, t) for t in getctx(thy, terms)]
        bot = thy[:tname][terms]
        push!(res, sequent(top, bot, thy[:aname][ax]))
    end
    return join(res, "\n")
end

#-------------

# print(theory(cat))
"""
Sorts
-----


----  Ob
Ob()

x₁:Ob x₂:Ob
-----------  Hom
Hom(x₁,x₂)


Operations
----------

    Γ:Ob
-------------  id
id(Γ) : HomΓΓ

A:Ob f:HomAB B:Ob C:Ob g:HomBC
------------------------------  comp
      comp(f,g) : HomAC


Axioms
------

a:Ob p:Homab b:Ob q:Hombc c:Ob d:Ob r:Homcd
-------------------------------------------  Associativity
             p.(q.r) = (p.q).r

  α:Ob f:Homαβ β:Ob
---------------------  Unit
f = id(α).f = f.id(β)
"""

function add_sort(thy::ACSet, constructor::String, argsorts::Vector{Int})::ACSetTransformation
    new = deepcopy(thy)
    add_parts!()
    return new
end
