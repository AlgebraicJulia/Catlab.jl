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

end