# MatchPy.jl

This package provides an implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

This algorithm finds all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The latter algorithm allocates much less and is generally an order faster, but does not disambiguate associative from commutative.

## Interface

Nothing is exported, so all methods must be qualified.

The primary method is `_eachmatch` which returns an iterator of matches.

The `MatchPy._match` method chooses the first of the possible matches given by `_eachmatch`, returning `nothing` if there are no matches.

The `MatchPy._rewrite` method replaces matches of a pattern in another expression.

The `MatchPy._replace` method walks through an expression, and can be used to replace parts of an expression with other parts.

### Examples

"Each" match

```@repl matchpy
julia> using MatchPy

julia> MatchPy._eachmatch(:(~x + ~y), :(a + b), MatchPy.MP()) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :b, :y => :a)
 Base.ImmutableDict(:x => :a, :y => :b)
```

Single match

```@repl matchpy
julia>  MatchPy._match(:(~x + ~y), :(a + b))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :a
  :y => :b

```

Replace:

```@repl matchpy
julia> MatchPy._replace(:(cos(2x)^2 + sin(2x)^2), :(sin(~x)^2 + cos(~x)^2) => 1)
1
```

The `_simplify` function builds on the above to perform some common simplifications:

```@repl matchpy
julia> MatchPy._simplify(:(cos(2x)^2 + sin(2x)^2))
:(1 + 0)
```

## Wildcards

Patterns are specified with wildcards or which there is a variety. We follow the specification of `SymbolicUtils`  (also implemented in `SymbolicIntegration.jl`, of which its `rule2` functionality was mined here for insight):

* A "slot variable", specified as `:(~x)`, matches one argument. For the MatchPy algorithm, an associative functions may have a slot variable match one or more arguments.

* A "default slot variable", specified as `:(~!x)`, matches 0 or 1 arguments. If there are 0 matches a default value is use (for an operation of `+` this is `0`, for `*` this is `1`, and for an exponent, also `1`).

* A "segment variable", specified `:(~~x)`, matches 0, 1 or more of the arguments. The match is returned as a collection of matches. (This is a "star" variable in MatchPy.)

* A "plus variable", specified as `:(~~~x)`, matches 1 or more of the arguments similar to a segment variable.

* Wildcards may have predicates or *guards* attached to them through the notation `:(~x::predicate)`. A match only occurs when the accompanying predicate is `true` for the proposed value.



### Examples

* Use of default slots

```
julia> MatchPy._replace(:(2cos(2x)^2 + 2sin(2x)^2), :(~!a * sin(~x)^2 + ~!a * cos(~x)^2) => :(~!a))
2

julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x + ~!c)^(~!m)), :(sin(2x))) |> collect
2-element Vector{Any}:
 Base.ImmutableDict{Symbol, Any}(:x => 2, :b => :x, :c => 0, :m => 1, :a => 1)
 Base.ImmutableDict{Symbol, Any}(:x => :x, :b => 2, :c => 0, :m => 1, :a => 1)
```

* Use of a predicate function to filter matches

```
julia> MatchPy._eachmatch(:(~!a * sin(~!b *~x::(u -> !isa(u,Number)) + ~!c)^(~!m)), :(sin(2x))) |> collect
1-element Vector{Any}:
 Base.ImmutableDict{Symbol, Any}(:x => :x, :b => 2, :c => 0, :m => 1, :a => 1)
```

* Use of a segment variable

```
julia> MatchPy._eachmatch(:(~x + ~~y), :(a + b)) |> collect
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b])
 Base.ImmutableDict(:x => :b, :y => Any[:a])
 Base.ImmutableDict(:x => :(a + b), :y => Any[])
```

Notice that `+` is associative, so the slot variable `~x` may match one or more arguments. In the case there is more than one, the function is called on them. This is why the first match has `:x => :(a+b)`. A match for a segment should always return a container.

* Plus variables must have aleast one match
```
julia> MatchPy._eachmatch(:(~x + ~~~y), :(a + b)) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b])
 Base.ImmutableDict(:x => :b, :y => Any[:a])
```

Compare to:

```
julia> MatchPy._eachmatch(:(~x + ~~y::(!isempty)), :(a + b)) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b])
 Base.ImmutableDict(:x => :b, :y => Any[:a])

julia> MatchPy._eachmatch(:(~x + ~~y), :(a + b)) |> collect
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b])
 Base.ImmutableDict(:x => :b, :y => Any[:a])
 Base.ImmutableDict(:x => :(a + b), :y => Any[])
```



For segment variables, MatchPy will try to identify all possibilities. Further, MatchPy has checks for *associativity* and *commutativity* and will call the operation on the identified matches We can see this with this example:

```
julia> MatchPy._eachmatch(:(~x + ~~y), :(a + b + c)) |> collect
7-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b, :c])
 Base.ImmutableDict(:x => :b, :y => Any[:a, :c])
 Base.ImmutableDict(:x => :(a + b), :y => Any[:c])
 Base.ImmutableDict(:x => :c, :y => Any[:a, :b])
 Base.ImmutableDict(:x => :(a + c), :y => Any[:b])
 Base.ImmutableDict(:x => :(b + c), :y => Any[:a])
 Base.ImmutableDict(:x => :(a + b + c), :y => Any[])


julia> MatchPy._eachmatch(:(~~x + ~~y), :(a + b + c)) |> collect
8-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => Any[], :y => Any[:a, :b, :c])
 Base.ImmutableDict(:x => Any[:a], :y => Any[:b, :c])
 Base.ImmutableDict(:x => Any[:b], :y => Any[:a, :c])
 Base.ImmutableDict(:x => Any[:a, :b], :y => Any[:c])
 Base.ImmutableDict(:x => Any[:c], :y => Any[:a, :b])
 Base.ImmutableDict(:x => Any[:a, :c], :y => Any[:b])
 Base.ImmutableDict(:x => Any[:b, :c], :y => Any[:a])
 Base.ImmutableDict(:x => Any[:a, :b, :c], :y => Any[])
 ```



Similarly:

 ```
julia> MatchPy._eachmatch(:(f(~~x, ~~y)), :(f(a,b,c))) |> collect
4-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => Any[], :x => Any[:a, :b, :c])
 Base.ImmutableDict(:y => Any[:c], :x => Any[:a, :b])
 Base.ImmutableDict(:y => Any[:b, :c], :x => Any[:a])
 Base.ImmutableDict(:y => Any[:a, :b, :c], :x => Any[])

```

This is not quite the same as the last example which uses `+` instead of `f`, as `f` is not assumed associative and commutative, so there are half as many matches.
