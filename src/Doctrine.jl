module Doctrine
export Category,
  MonoidalCategory, SymmetricMonoidalCategory,
  CompactClosedCategory,
  DaggerCategory, DaggerCompactCategory

include("doctrine/Category.jl")
include("doctrine/Monoidal.jl")
include("doctrine/Relations.jl")

end
