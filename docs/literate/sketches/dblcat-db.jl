using Catlab

# For the following discussion, we will "Set-valued functor" in place of "copresheaf" because it more clearly states the relationship between data when the restriction maps are trivial.

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
foreach(keys(df)) do student
    classes = df[student]
    student_id = add_part!(j, :Student, student_name=student)
    foreach(classes) do class
        class_id = incident(j, class, :class_name)
        if isempty(class_id); class_id = add_part!(j, :Class, class_name=class) end
        add_part!(j, :Junct, student=student_id, class=only(class_id))
    end
end

# This is well and good, but it introduces some boilerplate. For an ordinary relationship in data science, I have to add three lines in my schema and almost ten lines of code to source. But these meager additions to the code obscure the possibility of a more elegant design principle at play, here appearing as a proarrow between Students and Classes: 
p = @present SchSpan(FreeDoubleCategory) begin
    Student::Ob
    Class::Ob
    # produces junction table as well as "student" and "class" morphisms
    Junct::Pro(Student, Class)
end

df = Dict(1 => [1, 2, 3],
          2 => [4, 1, 5],
          3 => [6, 7, 3, 1])

# Here the proarrow encodes the double relationship the Junction table enjoys with both Student and Class tables, diagrammatically written as a `span` (Student <- Junction -> Class). With this construction, these relations are now captured with the expressiveness of double categories. However, AlgebraicJulia carries information via ACSets, so we need to define a functor sending presentations ThDoubleCategory to that of the ACSet. This code incompletely does that:

function acset(p::Presentation{ThDoubleCategory.Meta.T, Symbol})
    # construct ACSet presentation
    out = Presentation(FreeSchema)
    # add arguments
    obs = Ob.(Ref(FreeSchema.Ob), only.(args.(generators(p, :Ob))))
    map(obs) do ob
        add_generator!(out, ob)
    end
    # convert proarrows to homs
    map(generators(p, :Pro)) do pro
        ob = Ob(FreeSchema.Ob, first(pro))
        add_generator!(out, ob)
        map(pro.type_args) do hom
            name = Symbol(lowercase(string(only(hom.args))))
            add_generator!(out, Hom(name, ob, out[only(hom.args)]))
        end
    end
    out
end

# We now have a way of defining JunctionTables with the presentation of a Double Category. Notice that we have not defined AttrTypes, which in ACSet terminology are columns associated to the primary keys to each table. So we will refer to this schema as "vanilla," and instantiate the `VanillaJunctionType`

SchVanilla = acset(p)
@acset_type VanillaJunctionType(SchVanilla)
j = VanillaJunctionType()

# Now we just need the code to actually perform the data insertion. It'll need to insert data into both Student and Class tables as well as check for 

# TODO broken?
foreach(keys(df)) do student
    classes = df[student]
    student_id = add_part!(j, :Student)
    foreach(classes) do class
        class_id = incident(j, class)
        if isempty(class_id); class_id = add_part!(j, :Class, class_name=class) end
        add_part!(j, :Junct, student=student_id, class=only(class_id))
    end
end

# Real-world data of course has attributions. Let's go back to our first dataset example:

df = Dict(:Fiona => [:Math, :Philosophy, :Music],
          :Gregorio => [:Cooking, :Math, :CompSci],
          :Heather => [:Gym, :Art, :Music, :Math])

# Here, the data is presented as Julia Symbols representing the names for either students or classes. We'll call this AttrType "Name". So we will need to handle AttrTypes in our dpresentation, and in turn we need a theory of Double Categories with an additional set of proarrows responsible for AttrTypes. To accomplish this, we defined in the standard library a theory of "Double Schemas," which is the theory of Double Categories with the AttrType axioms copy-pasted into it. Now we can define this schema: 

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

# The `acset` function will need a method for the presentation of a `ThDoubleSchema`. We define that and two helper functions which just extract the name. 

Symbol(s::FreeDoubleSchema.AttrType{:generator}) = first(GATlab.args(s))
Symbol(s::FreeDoubleSchema.Attr{:generator}) = first(GATlab.args(s))

function acset(p::Presentation{ThDoubleSchema.Meta.T, Symbol})
    # construct ACSet presentation
    out = Presentation(FreeSchema)
    # add AttrType
    attrtypes = map(generators(p, :AttrType)) do attrtype
        add_generator!(out, AttrType(FreeSchema.AttrType, Symbol(attrtype)))
    end
    # add Obs arguments
    obs = Ob.(Ref(FreeSchema.Ob), only.(GATlab.args.(generators(p, :Ob))))
    map(obs) do ob
        add_generator!(out, ob)
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

SchAttr = acset(p)
@acset_type JunctionNameType(SchAttr)
j = JunctionNameType{Symbol}()

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


