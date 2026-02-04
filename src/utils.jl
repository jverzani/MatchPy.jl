# A substitution is a collection of pairs 𝑋 -> 𝐺
const MatchDict = Base.ImmutableDict{Symbol, Any}
FAIL_DICT = MatchDict(:_fail,0)
∅ = ()

match_dict() = MatchDict()

function match_dict(kvs::Pair...)
    σ = MatchDict()
    match_dict(σ, kvs...)
end

function match_dict(σ::MatchDict, kvs::Pair...)
    for (k,v) ∈ kvs
        if haskey(σ, k)
            σ[k] != v && return FAIL_DICT #error("repeated key with different value: $k => $v ($(σ[k]))")
        else
            σ = MatchDict(σ, k, v)
        end
    end
    σ
end

#  σ △ σ′ (\bigtriangleup) for every x in the intersection of the domains has same value
function iscompatible(σ::MatchDict, σ′::MatchDict)
    isempty(σ) && return true
    isempty(σ′) && return true
    for k in keys(σ)
        if haskey(σ′, k) # intersect(keys(σ), keys(σ′)) allocates
            σ[k] == σ′[k] || return false
        end
    end
    return true
end

# σ ⊔ σ′ (\sqcup) is union of two compatible matches
function merge_match(σ::MatchDict, σ′::MatchDict)
    # assume compatible
    for (k,v) ∈ σ′
        σ = match_dict(σ, k => v)
    end
    σ
end
merge_match(σ::Tuple, σ′::MatchDict) = σ′

function union_merge(θ, σ′)
    (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
end



## Expression related methods
"""
    as_symbol_or_literal(x)

Take `x` and return a symbol or literal (if possible) otherwise return `x`.

Used to compare a possibly symbolic value with a symbol or a number

This is also `SymbolicUtils.unwrap_const`.
"""
as_symbol_or_literal(x::Union{Real, Symbol, Expr}) = x
as_symbol_or_literal(x) = x
ϟ = as_symbol_or_literal #\koppa[tab]

# need to compare x and p when p is from an expression
# trick -- SymEngine.Basic <: Number
eq_expr(a, p::Number) = isequal(a,p)
eq_expr(a::Number, p::Symbol) = false
eq_expr(a, p::Symbol) = isequal(Symbol(a),p)

# create a term for a pattern (pterm) or a subject (sterm)
# the latter might involve a symbolic type
function pterm(op::Union{Expr,Symbol}, args; elide=true)
    if elide && length(args) == 1 && op ∈(:+, :*, :^, :/)
        return only(args)
    else
        Expr(:call, op, args...)
    end
end

# subject term
function sterm(T, op, args)
    _isexpr = T ∈ (Expr, Symbol, Real)
    if _isexpr
        !isa(op, Symbol) && (op = nameof(op))
    elseif !isexpr
        isa(op, Symbol) && (op = eval(op))
    end
    _isexpr ? pterm(op, args) : op(args...)
end

_isone(x) = isequal(x, 1)

_groupby(pred, t) = (t = filter(pred,t), f=filter(!pred, t))


# ----- predicates
_is_rational(x) = isa(ϟ(x), Rational)


# can override, say with :Symbol
iscommutative(op) = op ∈ (:+, :*, +, *)
isassociative(op) = op ∈ (:+, :*, +, *)

isassociative(::typeof(+)) = true
isassociative(::typeof(*)) = true

iscommutative(::typeof(+)) = true
iscommutative(::typeof(*)) = true



# check for wildcard variables
is_𝑋(x::Any) = false
has_𝑋(x::Any) = false
is_slot(x::Any) = false
is_defslot(x::Any) = false
is_segment(x::Any) = false
is_plus(x::Any) = false
is_op(x::Any) = false

const defslot_op_map = Dict(:+ => 0, :* => 1, :^ => 1, :/ => 1)

# Expr
is_𝑋(x::Expr) = (iscall(x) && first(x.args) === :(~))  ||
    (isexpr(x) && is_𝑋(first(x.args)))

function has_𝑋(x::Expr)
    is_𝑋(x) && return true
    !iscall(x) && return false
    is_𝑋(operation(x)) && return true
    any(has_𝑋, arguments(x))
end

function is_slot(x::Expr)
    is_𝑋(x) || return false
    _, x = x.args
    iscall(x) && return false
    return true
end

function is_defslot(x::Expr)
    #if is_operation(:^)(x)
    #    _,x = arguments(x)
    #end

    is_𝑋(x) || return false
    _, arg = x.args
    is_operation(:(!))(arg) && return true


    return false
end

is_slot_or_defslot(x) = is_slot(x) || is_defslot(x)

function is_segment(x::Expr)
    is_𝑋(x) || return false # first is ~
    h,x = x.args
    is_𝑋(h) && return false # an op
    is_𝑋(x) || return false # second is ~
    _,x = x.args
    is_𝑋(x) && return false
    return true
end

# ~~~x (1 or more)
function is_plus(x::Expr)
    is_𝑋(x) || return false
    _,x = x.args
    is_𝑋(x) || return false
    _,x = x.args
    is_𝑋(x) || return false
    return true
end

# (~G)(~x)
function is_op(x::Expr)
    is_𝑋(x) && iscall(x) && is_𝑋(operation(x))
end

# return symbol holding variable name
varname(x::Symbol) = x
function varname(x::Expr)
    if x.args[1] ∈ (:~, :!)
        varname(x.args[2])
    else
        varname(x.args[1])
    end
end

# return wildcard matches
# RENAME?
_free_symbols(::Any) = Expr[]
function _free_symbols(x::Expr)
    is_𝑋(x) && return [varname(x)]
    iscall(x) || return Expr[]
    unique(vcat(_free_symbols.(arguments(x))...))
end


# return bool, var (symbol name), pred
has_predicate(x::Symbol) = false
function has_predicate(x::Expr)
    if x.args[1] ∈ (:~, :!)
        has_predicate(x.args[2])
    else
        length(x.args) == 2 && x.head==:(::)
    end
end

# return symbol of function
get_predicate(x::Symbol) = :nothing
function get_predicate(x::Expr)
    if x.args[1] ∈ (:~, :!)
        get_predicate(x.args[2])
    else
        x.args[2]
    end
end


## Matching
# copy of  CallableExpressions.expression_map_matched(pred, mapping, u)
# if argument, `a`, matches via `is_match` replace with `f(a)`
function map_matched(ex, is_match, f)
    if !iscall(ex)
        return is_match(ex) ? f(ex) : ex
    else
        is_match(ex) && return f(ex)
        iscall(ex) || return ex
        children = map_matched.(arguments(ex), is_match, f)
        return sterm(typeof(first(children)), operation(ex), children)
    end
end

# if expression operation, `op`, matches via `is_match` replace with `f(op)`
function map_matched_head(ex, is_match, f)
    !iscall(ex) && return ex
    op = operation(ex)
    is_match(op) && (op = f(op))
    args′ = map_matched_head.(arguments(ex), is_match, f)
    T = typeof(first(args′))
    if T <: Expr || T <: Symbol || T <: Number
        return pterm(Symbol(op), args′)
    else
        return sterm(T, op, args′)
    end
end
