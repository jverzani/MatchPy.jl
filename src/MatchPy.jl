module MatchPy

# implement algorithm of matchpy paper through Ch. 3
# Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables by Manuel Krebber

using TermInterface
using Combinatorics: permutations, combinations

include("utils.jl")
include("syntactic_match.jl")
include("match_py.jl")
include("rule2a.jl")

include("_replace.jl")
end
