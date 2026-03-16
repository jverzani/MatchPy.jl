module MatchPy

using TermInterface
import Combinatorics: permutations, combinations, multiexponents



include("utils.jl")
include("syntactic_match.jl")
include("match_py.jl")
include("rule2a.jl")

include("replace.jl")
end
