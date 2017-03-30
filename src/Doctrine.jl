module Doctrine
export Category, Category2,
  MonoidalCategory, SymmetricMonoidalCategory,
  CompactClosedCategory,
  DaggerCategory, DaggerCompactCategory

include("doctrine/Category.jl")
include("doctrine/Monoidal.jl")
include("doctrine/Relations.jl")

end
