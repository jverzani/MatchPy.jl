# MatchPy

[![Build Status](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides an implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

This algorithm finds all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The MatchPy algorithm can separately match associatively *and* commutatively.

```
julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b + c));
  0.000071 seconds (60 allocations: 3.000 KiB)

julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b)) |> collect
  0.000203 seconds (527 allocations: 26.219 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => :b)
 Base.ImmutableDict(:x => :b, :y => :a)

julia> @time MatchPy._eachmatch(:(~x + ~y), :(a + b + c)) |> collect
  0.000233 seconds (1.46 k allocations: 70.125 KiB)
6-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => :(b + c))
 Base.ImmutableDict(:x => :b, :y => :(a + c))
 Base.ImmutableDict(:x => :(a + b), :y => :c)
 Base.ImmutableDict(:x => :c, :y => :(a + b))
 Base.ImmutableDict(:x => :(a + c), :y => :b)
 Base.ImmutableDict(:x => :(b + c), :y => :a)

 ```

The reduced number of allocations in the first call, is due to the values being returned as a generator. There are additional allocations when iterated by `collect`. The second example shows commutativity being employed, as `+` is assumed to be commutative. As well, `+` is assumed to be associative, so there are 6 matches in the last example, the first of which matches `:(a + (b+c))`.
