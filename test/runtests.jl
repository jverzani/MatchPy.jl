using Test
using AssociativeCommutativePatternMatching
using AssociativeCommutativePatternMatching: _eachmatch, _replace, _match


include("match-test.jl")
include("matchpy-test.jl")
VERSION >= v"1.12" && include("test-jet.jl")
