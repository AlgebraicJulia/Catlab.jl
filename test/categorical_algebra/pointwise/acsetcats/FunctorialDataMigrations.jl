module TestACSetFunctorialDataMigrations

using Test, Catlab

@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])

V, E, src, tgt = generators(SchGraph)
X, Φ = generators(SchDDS)


@present SchLabeledDDS <: SchDDS begin
  Label::AttrType
  label::Attr(X, Label)
end
@acset_type LabeledDDS(SchLabeledDDS, index=[:Φ, :label])

S, ϕ, Label, label = generators(SchLabeledDDS)
V, E, s, t, Weight, weight = generators(SchWeightedGraph)
const ℒ = FinCat(SchLabeledDDS)
const 𝒲 = FinCat(SchWeightedGraph)

ldds = LabeledDDS{Int}()
add_parts!(ldds, :X, 4, Φ=[2,3,4,1], label=[100, 101, 102, 103])

wg = WeightedGraph{Int}(4)
add_parts!(wg, :E, 4, src=[1,2,3,4], tgt=[2,3,4,1], weight=[101, 102, 103, 100])

@test wg == migrate(WeightedGraph{Int}, ldds,
  Dict(V => X, E => X, Weight => Label),
  Dict(src => id(S), tgt => Φ, weight => compose(Φ, label)); homtype=:hom)

@test Presentation(Graph(1)) == SchGraph
@test Presentation(ldds) == SchLabeledDDS

F = FinFunctor(
  Dict(V => S, E => S, Weight => Label),
  Dict(s => id(S), t => ϕ, weight => compose(ϕ, label)),
  𝒲, ℒ; homtype=:hom
)
ΔF = DataMigrationFunctor(F, LabeledDDS{Int}, WeightedGraph{Int})
@test wg == ΔF(ldds)

idF = id[FinCatC()](ℒ)
@test ldds == migrate(LabeledDDS{Int}, ldds, DeltaMigration(idF))


# Sigma Migrations of Attributed ACSets requires us to work in the category of VarACSets, as "freely" creating an ob with an attribute should assign an attribute variable as the attribute value.

end # module
