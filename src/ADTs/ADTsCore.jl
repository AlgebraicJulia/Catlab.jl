""" This module contains the basic components of an Abstract Term for constructing an ADT
"""

module ADTsCore

using MLStyle

export AbstractTerm

"""    AbstractTerm

The super type for all ADT types. This abstract type exists so that we can write generic methods that work on any term in any of the domain specific syntaxes.
For example, serializing to a Dictionary uses some reflection snippet that works for arbitrary types, but we only want to apply it to things that should be serialized like a Term.
"""
abstract type AbstractTerm end

""" Header 

1. Marks the header of our UWDModel. Provides basic metadata.
2. amr_to_string() allows us to represent the header as a string.
"""

@as_record struct Header <: AbstractTerm
  name::String
  schema::String
  description::String
  schema_name::String
  model_version::String
end

function header_to_string(header)
  @match header begin
    Header(name, s, d, sn, mv) => "\"\"\"\nASKE Model Representation: $name$mv :: $sn \n   $s\n\n$d\n\"\"\""
  end
end

end