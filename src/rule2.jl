# This is derived from https://github.com/JuliaSymbolics/SymbolicIntegration.jl/tree/main/src/methods/rule_based
# Licensed under MIT with Copyright (c) 2022 Harald Hofstätter, Mattia Micheletta Merlin, Chris Rackauckas, and other contributors

# TODO
# * rule condition inside the process? leads to faster cycling trough all the rules?
# * benchmark ImmutableDict vs. Dict
# * ~~x matches?

# Notes
#=
Variables include
* ~x a slot variable -- can match one part of an expression
* ~!x -- a defslot --- matches one part like a slot *or* defaults
* ~~x -- segment. Returns argument list of match

A match uses the *symbol* of a name (:x above).


=#


"""
data is a symbolic expression, we need to check if respects the rule
rule is a quoted expression, representing part of the rule
matches is the dictionary of the matches found so far

return value is a ImmutableDict
1) if a mismatch is found, FAIL_DICT is returned.
2) if no mismatch is found but no new matches either (for example in matching ^2), the original matches is returned
3) otherwise the dictionary of old + new ones is returned that could look like:
Base.ImmutableDict{Symbol, SymbolicUtils.BasicSymbolicImpl.var"typeof(BasicSymbolicImpl)"{SymReal}}(:x => a, :y => b)

The function checks in this order:
1) if the rule is a slot, like ~x or ~x::predicate
    proceed with checking in the matches or adding a new one if respects the predicate
2) if the rule contains a defslot in the arguments, like ~!a * ~x
    check first the normal expression (~a * ~x) and if fail check the non defslot part
3) if the rule contains a segment in the (only) argument, like +(~~x)
    confront operation with data and return match
4) otherwise for normal call confronts operation and arguments with data
    if operation of rule = +* does commutative checks
    do checks for negative exponent TODO
"""

#

using Combinatorics: permutations, combinations
using TermInterface

const MatchDict = Base.ImmutableDict{Symbol, Any}
ϟ = FAIL_DICT = MatchDict(:_fail,0)


__eachmatch(pat::Union{Symbol, Expr}, sub) = check_expr_r(sub, pat, [MatchDict()])

function __match(pat::Union{Symbol, Expr}, sub)
    σs = __eachmatch(pat, sub)
    _σ = iterate(σs)
    isnothing(_σ) ? _σ : first(_σ)
end

# return nothing if not a total match
function __replace(s::Expr, pat_r::Pair)
    pat, r = pat_r
    σ = __match(pat, s)
    fs = _free_symbols(r)
    if isnothing(σ)
        isempty(fs) && return r
        return nothing
    else
        Set(keys(σ)) == Set(fs) || error("didn't fill out all symbols")
        _rewrite(σ, r)
    end
end
__replace(s, pat_r, prs::Pair...) = foldl(__replace, prs; init=__replace(s, pat_r))

function _rewrite(σ::MatchDict, rhs)
    !iscall(rhs) && return rhs
    if is_𝑋(rhs)
        var = varname(rhs)
        if haskey(σ, var)
            return σ[var]
        else
            error("No match found for variable $(var)") #it should never happen
        end
    end
    # otherwise call recursively on arguments and then reconstruct expression
    args = [_rewrite(σ, a) for a ∈  arguments(rhs)]
    return mterm(operation(rhs), args)
end

# SymbolicUtils._isone -> _isone
# SymbolicUtils.unwrap_const -> unwrap_const

_isone(x) = isequal(x, 1)
_eval(pred, data) = !Base.invokelatest(Main.eval(pred), data)

_groupby(pred, t) = (t = filter(pred,t), f=filter(!pred, t))
function mterm(op, args)
    if length(args) == 1 && op ∈(:+, :*, :^, :-, :/)
        return only(args)
    else
        Expr(:call, op, args...)
    end
end

"""
    asexpr(x)
Take `x` and turn it into something that fits within an `Expr` object (Expr, Symbol, or Number)

Used to compare a possibly symbolic value with a symbol or a number
"""
asexpr(x::Union{Real, Symbol, Expr}) = x
asexpr(x) = Meta.parse(string(x))

iscommutative(op) = op ∈ (:+, :*)
isassociative(op) = op ∈ (:+, :*)

is_𝑋(x::Any) = false
is_slot(x::Any) = false
is_defslot(x::Any) = false
is_segment(x::Any) = false

is_𝑋(x::Expr) = iscall(x) && first(x.args) === :(~)
function is_slot(x::Expr)
    is_𝑋(x) || return false
    _, x = x.args
    iscall(x) && return false
    return true
end


const defslot_op_map = Dict(:+ => 0, :* => 1, :^ => 1)
function is_defslot(x::Expr)
    is_𝑋(x) || return false
    _, arg = x.args
    TermInterface.is_operation(:(!))(arg) && return true
    return false
end

function is_segment(x::Expr)
    is_𝑋(x) || return false # first is ~
    _,x = x.args
    is_𝑋(x) || return false # second is ~
    _,x = x.args
    is_𝑋(x) && return false
    return true
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
        length(x.args) == 2
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

# TODO matches does assignment or mutation? which is faster?
# TODO ~a*(~b*~c) currently will not match a*b*c . a fix is possible
# TODO rules with symbols like ~b * a currently cause error

# for when the rule contains a symbol, like ℯ, or a literal number
function check_expr_r(data, rule::Union{Real, Symbol}, σs)
    rule == asexpr(data) && return σs
    return MatchDict[]
end

# main function
function check_expr_r(data, rule::Expr, σs)

    if !iscall(rule)
        @show :what_is, rule
    end

    # rule is a single variable
    if is_𝑋(rule) #rule.head == :call && rule.args[1] == :(~)
        return just_variable(data, rule, σs)
    end


    # if there is a deflsot in the arguments
    i = findfirst(is_defslot, arguments(rule))
    if i !== nothing
        return has_defslot(i, data, rule, σs)
    end


    # check if a^defslot
#    if is_operation(:^)(rule)
#        a,b = arguments(rule)
#        if is_defslot(b)
#            error("handle this case")
#        end
#    end


    # rule is a normal call, check operation and arguments
    # XXX data Rational?
    if (operation(rule) == ://) && isa(data, Rational)
        return  has_rational(data, rule, σs)
    end

    !iscall(data) && return MatchDict[]

    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    # check opᵣ for special case
    if opᵣ ∈ (:^, :sqrt, :exp)
        return has_specialcased_op(data, rule, σs)
    end

    # gimmick to make Neim work in some cases:
    # * if data is a division transform it to a multiplication
    # (the final solution would be remove divisions form rules)
    # * if the rule is a product, at least one of the factors is a power, and data is a division

    neim_pass, arg_data, arg_rule = neim_rewrite(data, rule)
    opₛ != opᵣ && !neim_pass && return MatchDict[]

    # segments variables means number of arguments might not match
    if (any(is_segment, arg_rule))
        return has_any_segment(opₛ, arg_data, opᵣ, arg_rule,  σs)
    end

    (length(arg_data) != length(arg_rule)) && return MatchDict[]

    if iscommutative(opᵣ)
        return check_commutative(arg_data, arg_rule, σs)
    end

    # normal checks
    return ceoaa(arg_data, arg_rule, σs)
end

# check expression of all arguments
# elements of arg_rule can be Expr or Real
# TODO types of arg_data ??? SymsType[]
function XXceoaa(arg_data, arg_rule, σs)
    σ′′s = MatchDict[]
    for σ ∈ σs
        for (a, b) in zip(arg_data, arg_rule)
            σ′s = check_expr_r(a, b, [σ])
            !isempty(σ′s) && (σ′′s = union(σ′′s, σ′s))
        end
    end
    return σ′′s
end

function ceoaa(arg_data, arg_rule, σs)
    σ′s = σs
    for (a, b) in zip(arg_data, arg_rule)
        σ′s = check_expr_r(a, b, σ′s)
        isempty(σ′s) && return MatchDict[]
    end
    return σ′s
end

# match a single variable
function just_variable(data, rule, σs)
    @assert is_𝑋(rule)

    var = varname(rule)
    val = is_segment(rule) ? (data,) : data

    ms = MatchDict[]
    for σ ∈ σs
        if var in keys(σ) # if the slot has already been matched
            isequal(σ[var], val) && push!(ms, σ)
        else
            # if never been matched
            if has_predicate(rule)
                pred = get_predicate(rule)
                !_eval(pred, val) && continue
            end
            push!(ms, MatchDict(σ, var, val))
        end
    end
    return ms
end

function has_defslot(i, data, rule, σs)
    ps = copy(arguments(rule))
    pᵢ = ps[i]
    qᵢ = :(~$(pᵢ.args[2].args[2]))
    ps[i] = qᵢ

    # build rule expr without defslot and check it
    newr = mterm(operation(rule), ps)


    σ′s = check_expr_r(data, newr, σs)
    !isempty(σ′s) && return σ′s # had a match

    # if no normal match, check only the non-defslot part of the rule
    deleteat!(ps, i)
    tmp = mterm(operation(rule), ps)
    σs = check_expr_r(data, tmp, σs)

    var = varname(qᵢ)
    value = get(defslot_op_map, operation(rule), -1)
    return [MatchDict(σ, var, value) for σ ∈ σs if σ != ϟ]

end



function has_rational(data, rule, σs)
    # rational is a special case, in the integration rules is present only in between numbers, like 1//2

    as = arguments(rule)
    data.num == first(as) && data.den == last(as) && return σs
    # r.num == rule.args[2] && r.den == rule.args[3] && return matches::MatchDict
    return MatchDict[]
end

function has_specialcased_op(data, rule, σs)
    arg_data = arguments(data)
    arg_rule = arguments(rule)
    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    if opᵣ === :^
        # try first normal checks
        if (opₛ === :^)
            σ′s = ceoaa(arg_data, arg_rule, σs)
            !isempty(σ′s) && return σ′s
        end

        # try building frankestein arg_data (fad)
        fad = []

        is1divsmth = (opₛ == :/) && _isone(first(arg_data))

        if is1divsmth && iscall(arg_data[2]) && (operation(arg_data[2]) === ^)
            # if data is of the alternative form 1/(...)^(...)
            push!(fad, arguments(arg_data[2])[1], -1*arguments(arg_data[2])[2])

        elseif is1divsmth && iscall(arg_data[2]) && (operation(arg_data[2]) === sqrt)
            # if data is of the alternative form 1/sqrt(...), it might match with exponent -1//2
            push!(fad, arguments(arg_data[2])[1], -1//2)

        elseif is1divsmth && iscall(arg_data[2]) && (operation(arg_data[2]) === exp)
            # if data is of the alternative form 1/exp(...), it might match ℯ ^ -...
            push!(fad, ℯ, -1*arguments(arg_data[2])[1])

        elseif is1divsmth
            # if data is of the alternative form 1/(...), it might match with exponent = -1
            push!(fad, arg_data[2], -1)
        elseif (operation(data) === ^) && iscall(arg_data[1]) && (operation(arg_data[1]) === /) && SymbolicUtils._isone(arguments(arg_data[1])[1])
            # if data is of the alternative form (1/...)^(...)
            push!(fad, arguments(arg_data[1])[2], -1*arg_data[2])

        elseif operation(data)===exp
            # if data is a exp call, it might match with base e
            push!(fad, ℯ, arg_data[1])

        elseif operation(data)===sqrt
            # if data is a sqrt call, it might match with exponent 1//2
            push!(fad, arg_data[1], 1//2)

        else
            return MatchDict[]

        end

        return ceoaa(fad, arg_rule, σs)

    elseif opᵣ === :sqrt

        if (opₛ === :sqrt)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (arg_data[2] === 1//2)
            tocheck = arg_data[1]
        else
            return MatchDict[]
        end

        return ceoaa(tocheck, arg_rule, σs)

    elseif opᵣ === :exp

        if (opₛ === :exp)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (arg_data[1] === ℯ)
            tocheck = arg_data[2]
        else
            return MatchDict[]
        end

        return ceoaa(tocheck, arg_rule, σs)
    end
end

function neim_rewrite(data, rule)

    neim_pass = false

    arg_rule, arg_data = arguments(rule), arguments(data)
    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    if (opᵣ === :*) && any(is_operation(:^), arg_rule) && opₛ === :/

        #x->(isa(x,Expr) && x.head===:call && x.args[1]===:^), arg_rule) && (operation(data)===/)

        neim_pass = true

        n = arg_data[1]
        d = arg_data[2]

        # then push the denominator of data up with negative power
        sostituto = []

        if iscall(d) && opₛ == :^ #(operation(d)==^)

            a, b, c... =  arg_data
            push!(sostituto, a^b)

        elseif iscall(d) && opₛ == :*
            # push!(sostituto, map(x->x^-1,arguments(d))...)
            for factor in arguments(d)
                push!(sostituto, factor^-1)
            end
        else
            push!(sostituto, d^-1)
        end

        new_arg_data = []

        if iscall(n)
            if Symbol(operation(n)) === :*
                append!(new_arg_data, arguments(n))
            else
                push!(new_arg_data, n)
            end
        elseif !isone(n)
            push!(new_arg_data, n)
            # else dont push anything bc *1 gets canceled
        end

        append!(new_arg_data, sostituto)

        arg_data = new_arg_data

        # printdb(4,"Applying neim trick, new arg_data is $arg_data")
    end

    return (neim_pass, arg_data, arg_rule)
    #((Symbol(operation(data)) !== rule.args[1]) && !neim_pass) && return ϟ::MatchDict

end

function has_any_segment(opₛ, arg_data,
                         opᵣ, arg_rule, σ)

    seg, notseg = _groupby(is_segment, arg_rule)
    n,m = length(arg_data), length(notseg)

    if m > n
        return MatchDict[]
    elseif m == 0
        # assign all to the first!
        var = varname(first(seg))
        val = tuple(arg_data...) #Expr(:call, opₛ, arg_data...)
        σ′s = MatchDict[]
        for σ ∈ σs
            val′ = get(σ, var, missing)
            if ismissing(val′)
                σ′ = MatchDict(σ, var, val)
                push!(σ′s,σ′)
            elseif val == val′
                push!(σ′s,σ)
            end
        end# XXX?
    elseif 0 < m ≤ n
        σ′′s = MatchDict[]
        for ind ∈ combinations(1:n, m)
            sub′ = mterm(opₛ, arg_data[ind])
            pat′ = mterm(opᵣ, notseg)

            for σ ∈ σs
                σ′s = check_expr_r(sub′, pat′, [σ])
                if !isempty(σ′s)
                    # we found a match, assign the rest to first segment
                    for σ′ ∈ σ′s
                        var = varname(first(seg))
                        val = length(ind) < n ?
                            tuple(arg_data[setdiff(1:n, ind)]...) :
                            ()
                        val′ = get(σ′, var, missing)
                        if ismissing(val′)
                            σ′ = MatchDict(σ′, var, val)
                            push!(σ′′s, σ′)
                        elseif val == val′
                            push!(σ′′s, σ)
                        else
                            # continue the hunt
                        end
                    end
                end
            end
        end
        return σ′′s
    end
end

function check_commutative(arg_data, arg_rule, σs)
    # commutative checks
    σ′′s = MatchDict[]
    for arg_data′ in permutations(arg_data)
        σ′s = ceoaa(arg_data′, arg_rule, σs)
        !isempty(σ′s) && (σ′′s = union(σ′′s, σ′s))
    end
    return σ′′s
end

## ---------------

"""
recursively traverse the rhs, and if it finds a expression like:
Expr
  head: Symbol call
  args: Array{Any}((2,))
    1: Symbol ~
    2: Symbol m
substitute it with the value found in matches dictionary.
"""
function rewrite(matches::MatchDict, rhs::Expr)
    # printdb(3, "called rewrite with rhs $rhs")
    # if a expression of a slot, change it with the matches
    if is_𝑋(rhs)
        var = varname(rhs)
        if haskey(matches, var)
            return matches[var]
        else
            error("No match found for variable $(var)") #it should never happen
        end
    end
    # otherwise call recursively on arguments and then reconstruct expression
    args = [rewrite(matches, a) for a in arguments(rhs)]
    ## XXX this isn't correct if args is not Expr based
    return maketerm(eltype(args), operation(rhs), args, nothing)
end

# called every time in the rhs::Expr there is a symbol like
# - custom function names (contains_var, ...)
# - normal functions names (+, ^, ...)
# - nothing
rewrite(matches::MatchDict, rhs::Symbol) = rhs
rewrite(matches::MatchDict, rhs::Real) = rhs
rewrite(matches::MatchDict, rhs::String) = rhs::String
rewrite(matches::MatchDict, rhs::LineNumberNode) = nothing::Nothing
rewrite(matches::MatchDict, rhs::QuoteNode) = rhs::QuoteNode


function _replace(sub, rule::Pair{Expr, Expr})
    pat = first(rule)
    sub′ = Meta.parse(string(sub))
    m = __match(pat, sub′)
    isnothing(m) && return m
    r = rewrite(m, last(rule))
    r
end
