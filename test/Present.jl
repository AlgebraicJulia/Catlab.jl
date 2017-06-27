module TestPresentation

using Base.Test
using Catlab, Catlab.Doctrine

@present Company(FreeCategory) begin
  Employee::Ob
  Department::Ob
  Str::Ob
  
  first_name::Hom(Employee, Str)
  last_name::Hom(Employee, Str)
  manager::Hom(Employee, Employee)
  works_in::Hom(Employee, Department)
  secretary::Hom(Department, Employee)
  
  # Extra terminology.
  boss := manager
  second_level_manager := compose(manager, manager)
  third_level_manager := compose(manager, manager, manager)
  
  # Managers work in the same department as their employees.
  compose(manager, works_in) == works_in
  # The secretary of a department works in that department.
  compose(secretary, works_in) == id(Department)
end

# Check generators.
Employee, Department, Str = ob(FreeCategory, :Employee, :Department, :Str)
@test collect(values(generators(Company))) == [
  Employee,
  Department,
  Str,
  hom(:first_name, Employee, Str),
  hom(:last_name, Employee, Str),
  hom(:manager, Employee, Employee),
  hom(:works_in, Employee, Department),
  hom(:secretary, Department, Employee),
  hom(:boss, Employee, Employee),
  hom(:second_level_manager, Employee, Employee),
  hom(:third_level_manager, Employee, Employee),
]

# Check equations.
manager = hom(:manager, Employee, Employee)
works_in = hom(:works_in, Employee, Department)
secretary = hom(:secretary, Department, Employee)
@test collect(equations(Company)) == Equation[
  hom(:boss, Employee, Employee) => manager,
  hom(:second_level_manager, Employee, Employee) => compose(manager, manager),
  hom(:third_level_manager, Employee, Employee) => compose(manager, manager, manager),
  compose(manager, works_in) => works_in,
  compose(secretary, works_in) => id(Department),
]

end
