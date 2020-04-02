module TestMarkovCategories
using Test

using Catlab.Syntax, Catlab.WiringDiagrams
using Markov.MarkovCategories

# Doctrines
###########

A, B = Ob(FreeMarkovCategory, :A, :B)
M = Hom(:M, A, B)

# Domains and codomains
@test dom(expectation(M)) == A
@test codom(expectation(M)) == B

# Extra syntax
@test 𝔼(M) == expectation(M)

# LaTeX notation
@test sprint(show_latex, expectation(M)) == "\\mathbb{E}\\left(M\\right)"

# Wiring diagrams
#################

A, B, C = [ Ports{MarkovCategory.Hom}([sym]) for sym in [:A, :B, :C] ]
M = singleton_diagram(MarkovCategory.Hom, Box(:M,[:A],[:B]))
N = singleton_diagram(MarkovCategory.Hom, Box(:N,[:B],[:C]))

# Non-functoriality of expectation.
@test expectation(compose(M,N)) != compose(expectation(M),expectation(N))

end
