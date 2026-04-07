"""
MatchPy

A package implementing the algorithm matchpy from the paper "Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables" by Manuel Krebber (through section 3)

A match is a dictionary containing a mapping between wildcard values in the *pattern* with values in the *subject*.

Patterns are specified with expressions and within wildcards are specified by:

|Syntax | with predicate | note |
|:------|:---------------|:-----|
|`~x`   | `~x::pred`     | a slot variable to match a single argument |
|`~!x`   | `~!x`         | a default slot variable to match a single argument |
|`~~x`   | `~~x::pred`   | a star variable to match 0, 1 or more arguments |
|`~~~x`   | `~~~x::pred` | a plus variable to match 1 or more arguments |

The variable name is `x` in each of the above; variable names must be unique within a pattern (so one can't have both a `~x` and a `~~x`, though the same variable may appear more than once.

A predicate is a function, which can be evaluated in the scope of this package, that if `false` will prevent a match.

A default slot variable has default values for the enclosing operations of `+` (0), `*` (1),  and `^` (the exponent, also 1).

Matching is against arguments in a function or the function head. Functions may be associative and/or commutative. The matchpy algorithm allows the separation (as happens with matrix multiplication).

The pattern `f(a, ~x, c)` would match `f(a,b,c)` (with `:x => b`) but not match `f(a,b₁, b₂, c)`. Whereas `f(a, ~~x, c)` would match with `:x => [b₁, b₂]`.

For matchpy  and associative functions, matches have the function applied to slot variables. So `+(a,~x,c)` matched against `:(+(a, b₁, b₂, c))` would have `:x => :(b₁ + b₂)`.

The primary function is the unexported `_eachmatch(pat, sub`) function which returns an iterator of matches. The `_match(pat, sub)` function returns the first value. There are also `_rewrite` and `_replace` functions.
"""
module MatchPy

using TermInterface
import Combinatorics: permutations, combinations, multiexponents, powerset

include("utils.jl")
include("syntactic_match.jl")
include("match_py.jl")
include("replace.jl")
include("simplify.jl")
end
