""" Core components of an ADT
"""
module ADTsCore

"""    AbstractTerm

The super type for all ADT types. This abstract type exists so that we can write generic methods that work on any term in any of the domain specific syntaxes.
"""
abstract type AbstractTerm end

end