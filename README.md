# MatchPy

[![Build Status](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides two matching algorithms.

* An implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

* A slight modification of a matching algorithm developed in the `SymbolicIntegration` package in [rule2.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl). This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

Both find all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The latter algorithm allocates much less and is generally an order faster.

## Interface

The choice of which algorithm is specified by `MatchPy.R2()` (the default) or `MatchPy.MP()`. The matchpy algorithm returns a generator which can be collected.

The `MatchPy._match` method chooses the first of the possible matches given by `_eachmatch`, returning `nothing` if there are no matches.

The `MatchPy._replace` method can be used to replace parts of an expression with other parts.

### Examples

```
julia> using MatchPy

julia> MatchPy._eachmatch(:(~x + ~y), :(a + b))
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :b, :x => :a)
 Base.ImmutableDict(:y => :a, :x => :b)

julia> MatchPy._eachmatch(:(~x + ~y), :(a + b), MatchPy.MP()) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```

Replace:

```
julia> MatchPy._replace(:(cos(2x)^2 + sin(2x)^2), :(sin(~x)^2 + cos(~x)^2) => 1)
1
```

## Wildcards

Patterns are specified with wildcards or which there is a variety. We follow the specification of `SymbolicUtils`.

* A "slot variable", specified as `:(~x)`, matches one argument

* A "default slot variable", specified `:(~!x)`, matches 0 or 1 arguments. First, a slot variable is replaced to see if there is a match. If there is none, an attempt to find a match with the variable replaced by a default value (for an operation of `+` this is `0`, for `*` this is `1`, and for an exponent, also `1`.

* A "segment variable", specified `:(~~x)`, matches 0, 1 or more of the arguments. The match is returned as a tuple of matches.

In addition, for the MatchPy algorithm there is:

* A "plus variable", specified as `:(~~~x)`, matches 1 or more of the arguments similar to a segment variable.

Wildcards may have predicates attached to them through the notation `:(~x::predicate)`.

### Examples

```
# use of default slots
juliaMatchPy._replace(:(2cos(2x)^2 + 2sin(2x)^2), :(~!a * sin(~x)^2 + ~!a * cos(~x)^2) => :(~!a))
2

julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x + ~!c)^(~!m)), :(sin(2x)))
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => :x, :b => 2)
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => 2, :b => :x)

# use of predicate
julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x::(u -> !isa(u,Number)) + ~!c)^(~!m)), :(sin(2x)))
1-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => :x, :b => 2)

# ues of segment variable
julia> MatchPy._eachmatch(:(~x + ~~y), :(a + b), MatchPy.MP()) |> collect
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(a + b), :y => missing)
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)

# plus variable must have aleast one match
julia> MatchPy._eachmatch(:(~x + ~~~y), :(a + b), MatchPy.MP()) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```

The algorithms don't always give the same output. Here the segment variable for one is a tuple, but the MatchPy algorithm calls the `+` operation on the tuple, defaulting to `missing` when there are no arguments.

```
julia> MatchPy._eachmatch(:(~x + ~~y), :(+(a,b)))
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => (:b,), :x => :a)
 Base.ImmutableDict(:y => (:a,), :x => :b)
 Base.ImmutableDict(:x => :(a + b), :y => ())

julia> MatchPy._eachmatch(:(~x + ~~y), :(+(a,b)), MatchPy.MP()) |> collect
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(a + b), :y => missing)
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```
