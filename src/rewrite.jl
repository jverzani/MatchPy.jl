module Rewrite
# from https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl

## This stuff fails!!!
# * matching with segement and defslot
# matching (x+y)*sin(a + x + y) with ~~x * sin(~a + ~xx)
# maybe best to get matchpy working!!
# it fails on this too.

using TermInterface


# TODO rule condition inside the process? leads to faster cycling trough all the rules?
const SymsType = Any #SymbolicUtils.BasicSymbolic{SymbolicUtils.SymReal}
include("rule2.jl")
unwrap_const(x) = x

_match(pattern, subject) = check_expr_r(subject::SymsType, pattern::Expr, MatchDict())

end
