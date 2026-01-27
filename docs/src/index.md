# MatchPy.jl

This package provides two matching algorithms.

* An implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

* A slight modification of a matching algorithm developed in the `SymbolicIntegration` package in [rule2.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl). This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

Both find all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The latter algorithm allocates much less and is generally an order faster.

## Interface

The choice of which algorithm is specified by `MatchPy.R2()` (the default) or `MatchPy.MP()`. The matchpy algorithm returns a generator which can be collected.

The `MatchPy._match` method chooses the first of the possible matches given by `_eachmatch`, returning `nothing` if there are no matches.

The `MatchPy._replace` method can be used to replace parts of an expression with other parts.

### Examples

"Each" match

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

Single match

```
julia> MatchPy._match(:(~x + ~y), :(a + b), MatchPy.MP())
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :b
  :y => :a
```

Replace:

```
julia> MatchPy._replace(:(cos(2x)^2 + sin(2x)^2), :(sin(~x)^2 + cos(~x)^2) => 1)
1
```

## Wildcards

Patterns are specified with wildcards or which there is a variety. We follow the specification of `SymbolicUtils`.

* A "slot variable", specified as `:(~x)`, matches one argument.

* A "default slot variable", specified `:(~!x)`, matches 0 or 1 arguments. First, a slot variable is replaced to see if there is a match. If there is none, an attempt to find a match with the variable replaced by a default value (for an operation of `+` this is `0`, for `*` this is `1`, and for an exponent, also `1`.

* A "segment variable", specified `:(~~x)`, matches 0, 1 or more of the arguments. The match is returned as a tuple of matches.

In addition, for the MatchPy algorithm there is:

* A "plus variable", specified as `:(~~~x)`, matches 1 or more of the arguments similar to a segment variable.

Wildcards may have predicates attached to them through the notation `:(~x::predicate)`.

### Examples

* Use of default slots

```
juliaMatchPy._replace(:(2cos(2x)^2 + 2sin(2x)^2), :(~!a * sin(~x)^2 + ~!a * cos(~x)^2) => :(~!a))
2

julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x + ~!c)^(~!m)), :(sin(2x)))
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => :x, :b => 2)
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => 2, :b => :x)
```

* Use of predicate

```
julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x::(u -> !isa(u,Number)) + ~!c)^(~!m)), :(sin(2x)))
1-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:a => 1, :m => 1, :c => 0, :x => :x, :b => 2)
```

* Use of segment variable

```
julia> MatchPy._eachmatch(:(~x + ~~y), :(a + b), MatchPy.MP()) |> collect
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(a + b), :y => missing)
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```

* Plus variable must have aleast one match

```
julia> MatchPy._eachmatch(:(~x + ~~~y), :(a + b), MatchPy.MP()) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```

## Differences

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


The expectations aren't the same either. For segment variables, MatchPy will try to identify all possibilities. Further, MatchPy has checks for *associativity* and *commutativity* and will call the operation on the identified matches, `R2` only checks commutativity. But more importantly, doesn't try to identify all possible matches when there are two segment variables. We can see this with this example:

```
julia> MatchPy._eachmatch(:(~~x + ~~y), :(a + b + c), MatchPy.MP()) |> collect
8-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :(a + b + c), :y => missing)
 Base.ImmutableDict(:x => :(b + c), :y => :a)
 Base.ImmutableDict(:x => :(a + c), :y => :b)
 Base.ImmutableDict(:x => :c, :y => :(a + b))
 Base.ImmutableDict(:x => :(a + b), :y => :c)
 Base.ImmutableDict(:x => :b, :y => :(a + c))
 Base.ImmutableDict(:x => :a, :y => :(b + c))
 Base.ImmutableDict(:x => missing, :y => :(a + b + c))

julia> MatchPy._eachmatch(:(~~x + ~~y), :(a + b + c), MatchPy.R2())
1-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => (), :x => (:a, :b, :c))
 ```

 Similarly:

 ```
julia> MatchPy._eachmatch(:(f(~~x, ~~y)), :(f(a,b,c)), MatchPy.MP()) |> collect
4-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => Any[], :x => Any[:a, :b, :c])
 Base.ImmutableDict(:y => Any[:c], :x => Any[:a, :b])
 Base.ImmutableDict(:y => Any[:b, :c], :x => Any[:a])
 Base.ImmutableDict(:y => Any[:a, :b, :c], :x => Any[])

julia> MatchPy._eachmatch(:(f(~~x, ~~y)), :(f(a,b,c)), MatchPy.R2())
1-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => (), :x => (:a, :b, :c))
```

This is not quite the same as the last example, as `f` is not assumed associative and commutative (like `+`), so there are half as many matches.
