module TestPresentation

using Test
using Catlab, Catlab.Doctrines

# Presentation
##############

A, B, C = Ob(FreeCategory, :A, :B, :C)
f = Hom(:f, A, B)
g = Hom(:g, B, C)

# Generators
pres = Presentation()
@test !has_generator(pres, :A)
add_generator!(pres, A)
@test generators(pres) == [ A ]
@test generator(pres, :A) == A
@test has_generator(pres, :A)
add_generator!(pres, B)
@test generators(pres) == [ A, B ]
@test_throws Exception add_generator!(pres, A)

add_generators!(pres, (f,g))
@test generators(pres) == [ A, B, f, g ]
@test generators(pres, FreeCategory.Ob) == [ A, B ]
@test generators(pres, FreeCategory.Hom) == [ f, g ]
@test generators(pres, (:A, :B)) == [ A, B ]
@test generators(pres, [:f, :g]) == [ f, g ]

# Merge presentations
pres = Presentation()
add_generators!(pres, (A, B, f))
other = Presentation()
add_generators!(other, (B, C, g))
merge_presentation!(pres, other)
@test generator(pres, :f) == f
@test generator(pres, :g) == g
@test generators(pres, FreeCategory.Ob) == [ A, B, C ]
@test generators(pres, FreeCategory.Hom) == [ f, g ]

# Presentation macro
####################

@present Company(FreeCategory) begin
  # Primitive concepts.
  Employee::Ob
  Department::Ob
  Str::Ob
  
  first_name::Hom(Employee, Str)
  last_name::Hom(Employee, Str)
  manager::Hom(Employee, Employee)
  works_in::Hom(Employee, Department)
  secretary::Hom(Department, Employee)
  
  # Defined concepts.
  second_level_manager := compose(manager, manager)
  third_level_manager := compose(manager, manager, manager)
  
  # Abbreviations (no syntactic term for LHS).
  boss = manager
  
  # Managers work in the same department as their employees.
  compose(boss, works_in) == works_in
  # The secretary of a department works in that department.
  compose(secretary, works_in) == id(Department)
end

# Check generators.
Employee, Department, Str = Ob(FreeCategory, :Employee, :Department, :Str)
@test collect(generators(Company)) == [
  Employee,
  Department,
  Str,
  Hom(:first_name, Employee, Str),
  Hom(:last_name, Employee, Str),
  Hom(:manager, Employee, Employee),
  Hom(:works_in, Employee, Department),
  Hom(:secretary, Department, Employee),
  Hom(:second_level_manager, Employee, Employee),
  Hom(:third_level_manager, Employee, Employee),
]

# Check equations.
manager = Hom(:manager, Employee, Employee)
works_in = Hom(:works_in, Employee, Department)
secretary = Hom(:secretary, Department, Employee)
@test collect(equations(Company)) == Equation[
  Hom(:second_level_manager, Employee, Employee) => compose(manager, manager),
  Hom(:third_level_manager, Employee, Employee) => compose(manager, manager, manager),
  compose(manager, works_in) => works_in,
  compose(secretary, works_in) => id(Department),
]

# Check generators with compound type arguments.
@present C(FreeSymmetricMonoidalCategory) begin
  A::Ob
  B::Ob
  f::Hom(otimes(A,B),otimes(B,A))
  scalar::Hom(munit(),munit()) # Nullary case.
end
A, B = Ob(FreeSymmetricMonoidalCategory, :A, :B)
I = munit(FreeSymmetricMonoidalCategory.Ob)
@test generator(C, :f) == Hom(:f, otimes(A,B), otimes(B,A))
@test generator(C, :scalar) == Hom(:scalar, I, I)

# Serialization
###############

to_json(expr) = to_json_sexpr(Company, expr)
from_json(sexpr) = parse_json_sexpr(Company, FreeCategory, sexpr)

# To JSON
to_json(generator(Company, :Employee)) == "Employee"
to_json(generator(Company, :manager)) == "manager"
to_json(compose(generator(Company, :manager), generator(Company, :manager))) ==
  ["compose", "manager", "manager"]

# From JSON
@test from_json("Employee") == generator(Company, :Employee)
@test from_json("manager") == generator(Company, :manager)
@test from_json(["compose", "manager", "manager"]) ==
  compose(generator(Company, :manager), generator(Company, :manager))

end
