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

end
