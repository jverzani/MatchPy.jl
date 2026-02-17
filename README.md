# MatchPy

[![Build Status](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides two matching algorithms.

* An implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

* A slight modification of a matching algorithm developed in the `SymbolicIntegration` package in [rule2.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl). This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

Both find all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The "rule2a" algorithm allocates much less and is generally an order faster. The "matchpy" algorithm can match associatively and commutatively.

The difference might be seen here:

```
julia> @time S._eachmatch(:(~x + ~y), :(a + b))
  0.000063 seconds (110 allocations: 4.984 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :b, :x => :a)
 Base.ImmutableDict(:y => :a, :x => :b)

julia> @time S._eachmatch(:(~x + ~y), :(a + b + c))
  0.000011 seconds (29 allocations: 1.281 KiB)
Base.ImmutableDict{Symbol, Any}[]

julia> @time S._eachmatch(:(~x + ~y), :(a + b), MatchPy.MP()) |> collect
  0.000353 seconds (577 allocations: 33.219 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)

julia> @time S._eachmatch(:(~x + ~y), :(a + b + c), MatchPy.MP()) |> collect
  0.000269 seconds (1.51 k allocations: 84.453 KiB)
6-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(b + c), :y => :a)
 Base.ImmutableDict(:x => :(a + c), :y => :b)
 Base.ImmutableDict(:x => :c, :y => :(a + b))
 Base.ImmutableDict(:x => :(a + b), :y => :c)
 Base.ImmutableDict(:x => :b, :y => :(a + c))
 Base.ImmutableDict(:x => :a, :y => :(b + c))
 ```

 The second and fourth show the difference in associative matching where the matchpy algorithm (initiated by passing `MP()`) can match two items as `:a`, and `:(b + c)` by associating.

 The first and third show differences in the allocations and timing. The `_eachmatch` method for `MP()` returns a generator which is collected in the example. The allocations come when iterating:

 ```
 julia> @time σs = S._eachmatch(:(~x + ~y), :(a + b + c), MatchPy.MP());
  0.000040 seconds (71 allocations: 4.141 KiB)

julia> @time first(σs)
  0.000302 seconds (632 allocations: 31.781 KiB)
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :(b + c)
  :y => :a
```
