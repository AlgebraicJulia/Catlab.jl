using Catlab

# For the following discussion, we will "Set-valued functor" in place of "copresheaf" because it more clearly states the relationship between data when the restriction maps are trivial. It's also important to review the concept of a `Presentation`, which is tantamount to a finitely-presented model of a theory.

# It is common to receive many-to-many relations in data science. We can rearrange a many-many mapping into a Set-valued functor:
df = Dict(:Fiona => [:Math, :Philosophy, :Music],
          :Gregorio => [:Cooking, :Math, :CompSci],
          :Heather => [:Gym, :Art, :Music, :Math])

# Now how would we add this data to a table? In the ACSet framework, we might write this schema. Technically, we are defining a way of presenting relationships in the world of schema which we call `SchJunct`, which defines `Student`, `Class` tables with `name` and `subject` attributes respectively, as well as the object which represents the Junction table, which has two more attributes that play the role of connecting it to the tables we defined.
junction_schema = @present SchJunct(FreeSchema) begin
    Name::AttrType
    #
    Student::Ob
    name::Attr(Student, Name)
    #
    Class::Ob
    subject::Attr(Class, Name)
    #
    Junct::Ob
    student::Hom(Junct,Student)
    class::Hom(Junct,Class)
end

# We may add data to the junction table with the following code...
@acset_type JunctionTable(SchJunct)

# ...and then instantiate it...
j = JunctionTable{Symbol}()

# ...and then add the data...
function Base.insert!(j::JunctionTable{Symbol}, df::Dict{Symbol, Vector{Symbol}})
  foreach(keys(df)) do student
      classes = df[student]
      # check student exists
      student_id = incident(j, student, :name)
      if isempty(student_id); student_id = add_part!(j, :Student, name=student) end
      foreach(classes) do class
          class_id = incident(j, class, :subject)
          if isempty(class_id); class_id = add_part!(j, :Class, subject=class) end
          # enforce pair constraint
          id_pair = incident(j, only(student_id), :student) ∩ incident(j, only(class_id), :class)
          # TODO I added 'only' because incident will return e.g., [1] and not 1
          if isempty(id_pair); add_part!(j, :Junct, student=only(student_id), class=only(class_id)) end
      end
  end
  j
end

# Let's take a look

insert!(j, df)

# This junction table now defines a linkage between two different types of data. This is well and good, but it introduces some boilerplate. For what is a commonplace relationship in data science, I am in the unsympathetic position of having to add three lines in my schema and almost ten lines of code to source. But these meager requirements can obscure the fact that while the Junction Table is apparently just a table, its role in the database schema is to relate multiple tables together. Therefore it isn't really concerned with presenting data to the user the same way an ordinary table would, its instead a table being used to organize other tables. This role means that there might be a more elegant design principle at play which is capable of making this distinction. In double category theory, this takes the form of a proarrow between Students and Classes. Let's present a schema over the model of a different theory, `FreeDoubleSchema`,
#

p = @present SchSpan(FreeDoubleSchema) begin
    Name::AttrType
    #
    Student::Ob
    name::Attr(Student, Name)
    #
    Class::Ob
    subject::Attr(Class, Name)
    # produces junction table as well as "student" and "class" morphisms
    Junct::Pro(Student, Class)
end

# Here, the data is presented as Julia Symbols representing the names for either students or classes. We'll call this AttrType "Name". So we will need to handle AttrTypes in our presentation, and in turn we need a theory of Double Categories with an additional set of proarrows responsible for AttrTypes. To accomplish this, we defined in the standard library a theory of "Double Schemas," which is the theory of Double Categories with the AttrType axioms copy-pasted into it. 

# We'll now define a function called `ACSet` to convert the schema into that for an ACSet. We define that and two helper functions which just extract the name. 

Symbol(s::FreeDoubleSchema.AttrType{:generator}) = first(GATlab.args(s))
Symbol(s::FreeDoubleSchema.Attr{:generator}) = first(GATlab.args(s))
Symbol(s::FreeDoubleSchema.Ob{:generator}) = first(GATlab.args(s))

function ACSet(p::Presentation{ThDoubleSchema.Meta.T, Symbol})
    # construct ACSet presentation
    out = Presentation(FreeSchema)
    # add AttrType
    attrtypes = map(generators(p, :AttrType)) do attrtype
        add_generator!(out, AttrType(FreeSchema.AttrType, Symbol(attrtype)))
    end
    # add Obs
    map(generators(p, :Ob)) do ob
        add_generator!(out, Ob(FreeSchema.Ob, Symbol(ob)))
    end
    # add AttrVals
    map(generators(p, :Attr)) do attr
        add_generator!(out, Attr(Symbol(attr), [out[Symbol(t)] for t in attr.type_args]...))
    end
    # convert proarrows to homs
    map(generators(p, :Pro)) do pro
        ob = Ob(FreeSchema.Ob, first(pro))
        add_generator!(out, ob)
        map(pro.type_args) do hom
            name = Symbol(lowercase(string(only(hom.args)))) # XXX assumes the names are not yet taken
            add_generator!(out, Hom(name, ob, out[only(hom.args)]))
        end
    end
    out
end

# Let's instantiate the schema 
SchAttr = ACSet(p)
@acset_type JunctionNameTable(SchAttr)
j = JunctionNameTable{Symbol}()

function Base.insert!(j::JunctionNameTable{Symbol}, df::Dict{Symbol, Vector{Symbol}})
  foreach(keys(df)) do student
      classes = df[student]
      # check student exists
      student_id = incident(j, student, :name)
      if isempty(student_id); student_id = add_part!(j, :Student, name=student) end
      foreach(classes) do class
          class_id = incident(j, class, :subject)
          if isempty(class_id); class_id = add_part!(j, :Class, subject=class) end
          # enforce pair constraint
          id_pair = incident(j, only(student_id), :student) ∩ incident(j, only(class_id), :class)
          # TODO I added 'only' because incident will return e.g., [1] and not 1
          if isempty(id_pair); add_part!(j, :Junct, student=only(student_id), class=only(class_id)) end
      end
  end
  j
end

# Let's take a look
insert!(j, df)

# In database practice, junction tables are also just tables and, if your DBA is considerate, will be distinguished in name from other tables by, say, a prefix `J_`. However in the double theory perpsective, the junction table is a distinguished object. Therefore, we can treat it programmatically. The above INSERT code is for instance something we might be able to generalize with access to the junction table as a proarrow generator, `Pro(Student, Class)`. So we will go one step further by generating the INSERT code while we materialize the ACSet presentation.
