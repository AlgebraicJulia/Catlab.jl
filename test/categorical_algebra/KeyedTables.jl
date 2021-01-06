module TestKeyedTables

using Test
using Catlab.CategoricalAlgebra.KeyedTables
using Tables
using TypedTables

const TT = Table{NamedTuple{(:x,:y),Tuple{Symbol,Int}}}

kt = KeyedTable{Symbol,TT}()

push!(kt,(x=:foo,y=9),:a)

@test kt.x == [:foo]
@test Tables.istable(kt)
@test Tables.rowaccess(kt)
@test Tables.rows(kt) == kt
@test !Tables.columnaccess(kt)

# It seems to me like this doesn't work because of a bug in TypedTables...
# Or maybe I don't quite understand the Tables.jl interface
# @test Tables.getcolumn(kt,:x) = [:foo]

@test Tables.isrowtable(kt)
@test kt[:a,:y] == 9

kt[:a,:y] = 10

@test kt[:a,:y] == 10
@test kt[1,:y] == 10

kt2 = KeyedTable(Table(x=[:bar],y=[3]),[:b])

@test kt2[:b,:x] == :bar

append!(kt, kt2)

@test kt[:b,:x] == :bar
@test keys(kt) == keys(Dict(:a => 1, :b => 2))

setkey(kt,:a,:c)

@test kt[:c,:y] == 10
@test key(kt,1) == :c
@test index(kt,:c) == 1

kt[:b] = (x=:baz,y=40)

@test kt[:b,:y] == 40

end
