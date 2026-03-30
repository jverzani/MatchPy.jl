# MatchPy

[![Build Status](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides two matching algorithms.

* An implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

* A slight modification of a matching algorithm developed in the `SymbolicIntegration` package in [rule2.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl). This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

Both find all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The "rule2a" algorithm allocates much less and is generally an order faster. The "matchpy" algorithm can separately match associatively *and* commutatively.

The difference might be seen here:

```
julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b), MatchPy.R2())
  0.000038 seconds (88 allocations: 3.984 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :b, :x => :a)
 Base.ImmutableDict(:y => :a, :x => :b)

julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b + c), MatchPy.R2())
  0.000041 seconds (34 allocations: 1.516 KiB)
Base.ImmutableDict{Symbol, Any}[]

julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b), MatchPy.MP()) |> collect
  0.000161 seconds (548 allocations: 29.594 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)

julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b + c), MatchPy.MP()) |> collect
  0.000212 seconds (1.50 k allocations: 80.078 KiB)
6-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(b + c), :y => :a)
 Base.ImmutableDict(:x => :(a + c), :y => :b)
 Base.ImmutableDict(:x => :c, :y => :(a + b))
 Base.ImmutableDict(:x => :(a + b), :y => :c)
 Base.ImmutableDict(:x => :b, :y => :(a + c))
 Base.ImmutableDict(:x => :a, :y => :(b + c))
 ```

 The second and fourth show the difference in associative matching where the matchpy algorithm (initiated by default or by passing `MP()`) can match two items as `:a`, and `:(b + c)` by associating.

 The first and third show differences in the allocations and timing. The `_eachmatch` method for `MP()` returns a generator which is collected in the example. The allocations come when iterating:

 ```
julia> @time σs = MatchPy._eachmatch(:(~x + ~y), :(a + b + c), MatchPy.MP());
  0.000062 seconds (70 allocations: 4.266 KiB)

julia> @time first(σs)
  0.000133 seconds (602 allocations: 28.609 KiB)
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :(b + c)
  :y => :a
```
