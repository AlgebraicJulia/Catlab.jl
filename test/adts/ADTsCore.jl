""" ADT Core Tests
 
The following module checks the simple components of a generic ADT structure.
"""
module ADTsCoreTests

using Test
using Catlab.ADTs.ADTsCore

# Test Header Struct

@testset "Header Tests" begin
  #Check Proper Construction
  header = ADTsCore.Header("name1", "Schema1", "Description1", "SchemaName1", "Version1")

  @test header.name == "name1"
  @test header.schema == "Schema1"
  @test header.description == "Description1"
  @test header.schema_name == "SchemaName1"
  @test header.model_version == "Version1"

  #Check to String Representation
  string_header_result = ADTsCore.header_to_string(header)
  expected_string = "\"\"\"\nASKE Model Representation: name1Version1 :: SchemaName1 \n   Schema1\n\nDescription1\n\"\"\""
  @test string_header_result == expected_string

end

end