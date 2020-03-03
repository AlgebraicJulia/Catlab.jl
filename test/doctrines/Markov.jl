# Markov category
#################

A, B = Ob(FreeMarkovCategory, :A, :B)
M = Hom(:M, A, B)

# Domains and codomains
@test dom(expectation(M)) == A
@test codom(expectation(M)) == B

# Extra syntax
@test 𝔼(M) == expectation(M)

# LaTeX notation
@test latex(expectation(M)) == "\\mathbb{E}\\left(M\\right)"
