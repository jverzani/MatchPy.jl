# MatchPy.jl

This package provides an implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

This algorithm finds all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. Subjects can be expressions or perhaps other symbolic representations that satisfy the `TermInterface` specification.

## Interface

Nothing is exported, so all methods must be qualified.

The primary method is `_eachmatch` which returns an iterator of matches.

The `MatchPy._match` method chooses the first of the possible matches given by `_eachmatch`, returning `nothing` if there are no matches.

The `MatchPy._rewrite` method replaces matches of a pattern in another expression.

The `MatchPy._replace` method walks through an expression, and can be used to replace parts of an expression with other parts.

### Examples

"Each" match

```@repl matchpy
using MatchPy

MatchPy._eachmatch(:(~x + ~y), :(a + b)) |> collect
```

Single match

```@repl matchpy
MatchPy._match(:(~x + ~y), :(a + b))
```

Replace:

```@repl matchpy
MatchPy._replace(:(cos(2x)^2 + sin(2x)^2), :(sin(~x)^2 + cos(~x)^2) => 1)
```

The `_simplify` function builds on the above to perform some common simplifications:

```@repl matchpy
MatchPy._simplify(:(cos(2x)^2 + sin(2x)^2))
```

## Wildcards

Patterns are specified with wildcards of which there is a variety. We follow the specification of `SymbolicUtils`  (also implemented in `SymbolicIntegration.jl`, of which its `rule2` functionality was mined here for insight):

* A "slot variable", specified as `:(~x)`, matches one argument of an enclosing operation. For the MatchPy algorithm, an associative function may have a slot variable match one or more arguments.

* A "default slot variable", specified as `:(~!x)`, matches 0 or 1 arguments. If there are 0 matches a default value is used (for an operation of `+` this is `0`, for `*` this is `1`, and for an exponent, also `1`).

* A "segment variable", specified `:(~~x)`, matches 0, 1, or more of the arguments. The match is returned as a collection of matches. (This is a "star" variable in MatchPy.)

* A "plus variable", specified as `:(~~~x)`, matches 1 or more of the arguments, similar to a segment variable.

* Wildcards may have predicates or *guards* attached to them through the notation `:(~x::predicate)`. A match only occurs when the accompanying predicate is `true` for the proposed value.



### Examples

* Use of default slots

```@repl matchpy
r = :(~!a * sin(~x)^2 + ~!a * cos(~x)^2) => :(~!a)

MatchPy._replace(:(2cos(2x)^2 + 2sin(2x)^2), r)

MatchPy._eachmatch(:(~!a * sin(~!b *~x + ~!c)^(~!m)), :(sin(2x))) |> collect
```

* Use of a predicate function to filter matches

```@repl matchpy
MatchPy._eachmatch(:(~!a * sin(~!b *~x::(!Base.Fix2(isa, Number)) + ~!c)^(~!m)), :(sin(2x))) |> collect
```

(There are scoping issues with predicates to iron out, due to the use of `eval`.)

* Use of a segment variable

```@repl matchpy
MatchPy._eachmatch(:(~x + ~~y), :(a + b)) |> collect
```

Notice that `+` is associative, so the slot variable `~x` may match one or more arguments. In the case there is more than one, the function is called on them. This is why the first match has `:x => :(a+b)`. A match for a segment should always return a container.

* Plus variables must have aleast one match

```@repl matchpy
MatchPy._eachmatch(:(~x + ~~~y), :(a + b)) |> collect
```

This same result can also be achieved with an appropriate predicate:

```@repl matchpy
MatchPy._eachmatch(:(~x + ~~y::(!isempty)), :(a + b)) |> collect
```



For segment variables, MatchPy will try to identify all possibilities. Further, MatchPy has checks for *associativity* and *commutativity* of the operation and will call the operation on the identified associative matches.

This can lead to a combinatorially large number of matches:

```@repl matchpy
MatchPy._eachmatch(:(~x + ~~y), :(a + b + c)) |> collect
```

The assumption of associativity can lead to many more matches. In this example, the first match, which uses `+` instead of `f`, has twice the number of matches, as `f` which is not assumed associative or commutative.

```@repl matchpy
MatchPy._eachmatch(:(~~x + ~~y), :(a + b + c)) |> collect
MatchPy._eachmatch(:(f(~~x, ~~y)), :(f(a,b,c))) |> collect
```

That `+` is commutative, allows a segment variable to use a standard order for a match, which matches the order of no assumption on commutivity.

Commutivity and associativity are checked by the internal functions `iscommutative` and `isassociative` which are passed the operation of the subject (not the pattern, though in these examples the distinction is not important). Unless overridden, any of `+`, `:+`, `*`, `:*` are assumed both associative and commutive.

We can see the difference here:

```@repl matchpy
MatchPy.iscommutative(x::Symbol) = x ∈ (:(+), :(*), :fₘ)
MatchPy._eachmatch(:(fₘ(~x, ~y)), :(fₘ(a,b))) |> collect
MatchPy._eachmatch(:(f(~x, ~y)), :(f(a,b))) |> collect
```
