# For dispatch
abstract type MatchType end
struct MP <: MatchType end
struct R2 <: MatchType end

### ---- match, eachmatch, replace

function _match(pat::Union{Symbol, Expr}, sub, M::MatchType=R2())
    σs = _eachmatch(pat, sub, M)
    σ = iterate(σs)
    isnothing(σ) && return nothing
    first(σ)
end


# return iterator of each possible match
_eachmatch(pat::Expr, ex) = _eachmatch(pat, ex, R2())

function _eachmatch(pat::Expr, ex, M::MP)
    if has_𝑋(pat)
        return match_one_to_one([ex], pat)
    else
        σ = syntactic_match(ex, pat)
        return isnothing(σ) ? () : (σ,)
    end
end

function _eachmatch(pat::Union{Symbol, Expr}, sub, M::R2)
    check_expr_r(sub, pat, [MatchDict()])
end


# replace variables in rhs with values looked upin σ
# return an Expr (or Symbol or literal number)
function rewrite(σ::MatchDict, rhs::Expr, M::MatchType=R2())
    if !iscall(rhs)
        if isexpr(rhs)
            args = [rewrite(σ, a, M) for a ∈ children(rhs)]
            return Expr(head(rhs), args...)
        else
            return rhs
        end
    end

    if is_𝑋(rhs)
        var = varname(rhs)
        if haskey(σ, var)
            return σ[var]
        else
            error("No match found for variable $(var)") #it should never happen
        end
    end

    # otherwise call recursively on arguments and then reconstruct expression
    args = [rewrite(σ, a, M) for a ∈  arguments(rhs)]
    return pterm(operation(rhs), args; elide=false)
end

rewrite(matches::MatchDict, rhs::Symbol, M=nothing) = rhs::Symbol
rewrite(matches::MatchDict, rhs::Real, M=nothing) = rhs::Real
rewrite(matches::MatchDict, rhs::String, M=nothing) = rhs::String
rewrite(matches::MatchDict, rhs::LineNumberNode, M=nothing) = nothing::Nothing
rewrite(matches::MatchDict, rhs::QuoteNode, M=nothing) = rhs::QuoteNode


"""
    _replace(ex, args::Pair...)

Replace parts of an expression with something else.

Returns a symbolic object of same types as `ex`

The replacement is specified using `variable => value`; these are processed left to right.

There are different methods depending on the type of key in the the `key => value` pairs specified:

* A function call can be replaced by passing in a pair `𝐹 => 𝐹`, (e.g. `sin=>cos`)
* a variable, say `a` can be replaced by passing in  a pair like `a => a^2`
* an expression can be replaced similarly.
* For wildcard matching, an expression is used on both sides, as in `:(cos(~x)) => :(sin(~x))`.

The first three are straightforward. First, for function heads:

```@repl replace
julia> using SymEngine

julia> using MatchPy; import MatchPy: _replace

julia> @vars x p
(x, p)

julia> _replace(cos(x) - cos(x^2), cos => sin)
sin(x) - sin(x^2)
```

(See below for a hack when the function head is `exp`.)

For symbolic variables, we have:

```@repl replace
julia> ex = cos(x) - x*p
-p*x + cos(x)

julia> _replace(ex, x => 2*one(x))
-2*p + cos(2)

julia> _replace(ex, p => 2*one(x))
-2*x + cos(x)
```

For symbolic expressions, we have:


```@repl replace
julia> ex = cos(x)^2 + cos(x) + 1
(cos(x) ^ 2) + cos(x) + 1

julia> _replace(ex, cos(x) => x)
(x ^ 2) + x + 1
```

Replacements occur only if an entire node in the expression tree is matched:

```@repl replace
julia> u = 1 + x
1 + x

julia> replace(u + exp(-u), u => x^2)
1 + x + exp(-x ^ 2)
```

(As this addition has three terms, `1+x` is not a subtree in the expression tree.)


The last needs more explanation, as there can be wildcards in the expression.

Wildcards have a naming convention:

* `~x` to match a single part of an expression (possibly all arguments to a function)
* `~!x` like previous, only has a default value when operation is `+`, `*`, or `^`.
* `~~x` match 0, 1, or more variables
* `~~x` match 1 or more variables

```@repl replace
julia> _replace(cos(pi + x^2), :(cos(pi + ~x)) => :(-cos(~x)))
-cos(x ^ 2)

```

```@repl replace
julia> ex = log(sin(x)) + tan(sin(x^2))
log(sin(x)) + tan(sin(x ^ 2))

julia> _replace(ex, :(sin(~x)) => :(tan((~x) / 2)))
log(tan(x / 2)) + tan(tan((1/2) * x ^ 2)

julia> _replace(ex, :(sin(~x)) => :(~x))
log(x) + tan(x ^ 2)

julia> _replace(x*p, :((~x) * x) => :(~x) )
p
```

## Picture

The `AbstractTrees` package can print this tree-representation of the expression `ex = sin(x + x*log(x) + cos(x + p + x^2))`:

```
julia> print_tree(ex;maxdepth=10)
sin
└─ +
   ├─ x
   ├─ *
   │  ├─ x
   │  └─ log
   │     └─ x
   └─ cos              <--
      └─ +             ...
         ├─ x          <--
         ├─ p          ...
         └─ ^          ...
            ├─ x       ...
            └─ 2       ...
```

The command wildcard expression `:(cos(x + ~x))` looks at the part of the tree that has `cos` as a node, and the lone child is an expression with node `+` and child `x`. The `~x then matches `p + x^2`.


"""
function _replace(ex, uv::Pair, M::MatchType=R2())
    u,v = uv

    # Expr
    isa(u, Expr) && return _replace_arguments(ex, u, v, M)

    # is u function replace head
    isa(u, Function) && return map_matched_head(ex, ==(Symbol(u)), _ -> v)

    # is u variable, replace exact
    return map_matched(ex, ==(u), _ -> v)
end


function _replace_arguments(ex::Expr, u, v, M::MatchType)
    __replace_arguments(ex, u, v, M)
end
function _replace_arguments(ex, u, v, M::MatchType)
    __replace_arguments(ex, u, v, M) |> eval
end

# return Expression
function __replace_arguments(ex, u, v, M::MatchType)
    iscall(ex) || return (ex == u ? v : ex)

    σ = _match(u, ex, M) # sigma is nothing, (), or a substitution

    if !isnothing(σ)
        σ == () && return v # no substitution
        return rewrite(σ, v, M)
    end

    # peel off
    op, args = Symbol(operation(ex)), arguments(ex)
    args′ = __replace_arguments.(args, (u,), (v,), (M,))
    return pterm(op, args′)

end
