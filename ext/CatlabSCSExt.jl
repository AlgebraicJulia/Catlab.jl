module CatlabSCSExt

using SCS

import Catlab.Graphics.WiringDiagramLayouts: solve_isotonic

solve_isotonic(y::Vector, solver::Nothing; kw...) = solve_isotonic(y, SCS.Optimizer; kw...)

end
