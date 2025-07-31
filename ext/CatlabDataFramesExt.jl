module CatlabDataFramesExt

using Catlab.WiringDiagrams.WiringDiagramAlgebras: MaybeDataFrame
using DataFrames: DataFrame

import Catlab.WiringDiagrams.WiringDiagramAlgebras: make_table

make_table(::Type{MaybeDataFrame}, columns, names) =
  make_table(DataFrame, columns, names)

end # module
