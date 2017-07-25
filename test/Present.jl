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
Employee, Department, Str = Ob(FreeCategory, :Employee, :Department, :Str)
@test collect(values(generators(Company))) == [
  Employee,
  Department,
  Str,
  Hom(:first_name, Employee, Str),
  Hom(:last_name, Employee, Str),
  Hom(:manager, Employee, Employee),
  Hom(:works_in, Employee, Department),
  Hom(:secretary, Department, Employee),
  Hom(:boss, Employee, Employee),
  Hom(:second_level_manager, Employee, Employee),
  Hom(:third_level_manager, Employee, Employee),
]

# Check equations.
manager = Hom(:manager, Employee, Employee)
works_in = Hom(:works_in, Employee, Department)
secretary = Hom(:secretary, Department, Employee)
@test collect(equations(Company)) == Equation[
  Hom(:boss, Employee, Employee) => manager,
  Hom(:second_level_manager, Employee, Employee) => compose(manager, manager),
  Hom(:third_level_manager, Employee, Employee) => compose(manager, manager, manager),
  compose(manager, works_in) => works_in,
  compose(secretary, works_in) => id(Department),
]

end
