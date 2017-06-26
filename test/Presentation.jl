module TestPresentation

using Base.Test
using Catlab

@presents Company(FreeCategory) begin
  Employee::Ob
  Department::Ob
  
  first_name::Hom(Employee, String)
  last_name::Hom(Employee, String)
  manager::Hom(Employee, Employee)
  works_in::Hom(Employee, Department)
  secretary::Hom(Department, Employee)
  
  id(Department) == compose(secretary, works_in)
end

end
