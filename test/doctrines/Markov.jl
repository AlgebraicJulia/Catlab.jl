# Markov category
#################

A, B = Ob(FreeMarkovCategory, :A, :B)
M = Hom(:M, A, B)

# Expectations
@test dom(expectation(M)) == A
@test codom(expectation(M)) == B
@test latex(expectation(M)) == "\\mathbb{E}\\left(M\\right)"
