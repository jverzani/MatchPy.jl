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



using Combinatorics: permutations, combinations
using TermInterface

const MatchDict = Base.ImmutableDict{Union{Expr, Symbol}, Any}
const FAIL_DICT = MatchDict(:_fail, 0)
ϟ = FAIL_DICT

const op_map = Dict(:+ => 0, :* => 1, :^ => 1)

# SymbolicUtils._isone -> _isone
# SymbolicUtils.unwrap_const -> unwrap_const

_isone(x) = isone(x)
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

__match(pat, sub) = check_expr_r(sub, pat, MatchDict())


# for when the rule contains a symbol, like ℯ, or a literal number
function check_expr_r(data, rule::Union{Real, Symbol}, matches::MatchDict)
    rule == asexpr(data) && return matches
    return ϟ
end

# main function
function check_expr_r(data, rule::Expr, matches::MatchDict)::MatchDict
    if !iscall(rule)
        @show :what_is, rule
    end
    @show :check, data, rule, matches

    # rule is a single variable
    if is_𝑋(rule) #rule.head == :call && rule.args[1] == :(~)
        return just_variable(data, rule, matches)
    end


    # if there is a deflsot in the arguments
    i = findfirst(is_defslot, arguments(rule))
    if i !== nothing
        return has_defslot(data, rule, matches, i)
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
        return  has_rational(data, rule, matches)
    end

    !iscall(data) && return ϟ::MatchDict

    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    # check opᵣ for special case
    if opᵣ ∈ (:^, :sqrt, :exp)
        return has_specialcased_op(data, rule, matches)
    end

    # gimmick to make Neim work in some cases:
    # * if data is a division transform it to a multiplication
    # (the final solution would be remove divisions form rules)
    # * if the rule is a product, at least one of the factors is a power, and data is a division

    neim_pass, arg_data, arg_rule = neim_rewrite(data, rule, matches)
    opₛ != opᵣ && !neim_pass && return ϟ

    # segments variables means number of arguments might not match
    if (any(is_segment, arg_rule))
        return has_any_segment(opₛ, arg_data, opᵣ, arg_rule,  matches)
    end

    (length(arg_data) != length(arg_rule)) && return ϟ::MatchDict

    if iscommutative(opᵣ)
        @show :XXX_is_commutative, arg_rule, arg_data
        @show matches
        return check_commutative(opₛ, arg_data, opᵣ, arg_rule, matches)
    end

    # normal checks
    return ceoaa(arg_data, arg_rule, matches)::MatchDict
end

# check expression of all arguments
# elements of arg_rule can be Expr or Real
# TODO types of arg_data ??? SymsType[]
function ceoaa(arg_data, arg_rule, matches)
    for (a, b) in zip(arg_data, arg_rule)
        @show :ceoaa, a, b, matches
        matches = check_expr_r(a, b, matches)
        @show :ceoaa, matches
        matches === ϟ && return ϟ
        # else the match has been added (or not added but confirmed)
    end
    return matches
end

# match a single variable
function just_variable(data, rule, matches)
    @assert is_𝑋(rule)

    var = varname(rule)
    val = is_segment(rule) ? (data,) : data

    if var in keys(matches) # if the slot has already been matched
        !isequal(matches[var], val) && return ϟ::MatchDict
        return matches
    else
        # if never been matched
        if has_predicate(rule)
            pred = get_predicate(rule)
            _eval(pred, val) && return ϟ
            return MatchDict(matches, var, val)
        end
        # if no predicate add match
        return MatchDict(matches, var, val)
    end
end

function has_defslot(data, rule, matches, i)
    ps = copy(arguments(rule))
    pᵢ = ps[i]
    qᵢ = :(~$(pᵢ.args[2].args[2]))
    ps[i] = qᵢ

    # build rule expr without defslot and check it
    newr = mterm(operation(rule), ps)


    σ = check_expr_r(data, newr, matches)
    σ !== ϟ && return σ

    # if no normal match, check only the non-defslot part of the rule
    deleteat!(ps, i)
    tmp = mterm(operation(rule), ps)
    σ = check_expr_r(data, tmp, matches)

    # if yes match
    if σ !== ϟ
        value = get(op_map, operation(rule), -1)
        return MatchDict(σ, varname(qᵢ), value)
    end
    return ϟ
end



function has_rational(data, rule, matches)
    # rational is a special case, in the integration rules is present only in between numbers, like 1//2

    as = arguments(rule)
    data.num == first(as) && data.den == last(as) && return matches
    # r.num == rule.args[2] && r.den == rule.args[3] && return matches::MatchDict
    return ϟ
end

function has_specialcased_op(data, rule, matches)
    arg_data = arguments(data)
    arg_rule = arguments(rule)
    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    if opᵣ === :^
        # try first normal checks
        if (opₛ === :^)
            rdict = ceoaa(arg_data, arg_rule, matches)
            rdict !== ϟ && return rdict::MatchDict
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
            return ϟ::MatchDict

        end

        return ceoaa(fad, arg_rule, matches)::MatchDict

    elseif opᵣ === :sqrt

        if (opₛ === :sqrt)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (arg_data[2] === 1//2)
            tocheck = arg_data[1]
        else
            return ϟ::MatchDict
        end

        return ceoaa(tocheck, arg_rule, matches)::MatchDict

    elseif opᵣ === :exp

        if (opₛ === :exp)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (arg_data[1] === ℯ)
            tocheck = arg_data[2]
        else
            return ϟ::MatchDict
        end

        return ceoaa(tocheck, arg_rule, matches)::MatchDict
    end
end

function neim_rewrite(data, rule, matches)

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
                         opᵣ, arg_rule, matches)

    seg, notseg = _groupby(is_segment, arg_rule)
    n,m = length(arg_data), length(notseg)

    if m > n
        @show m,n
        return ϟ
    elseif m == 0
        @show m
        # assign all to the first!
        var = varname(first(seg))
        val = tuple(arg_data...) #Expr(:call, opₛ, arg_data...)
        val′ = get(matches, var, missing)
        if ismissing(val′)
            matches = MatchDict(matches, var, val)
            return matches
            elseif val == val′
            return matches
        else
            return ϟ
        end
    elseif 0 < m ≤ n
            for ind ∈ combinations(1:n, m)
                sub′ = mterm(opₛ, arg_data[ind])
                pat′ = mterm(opᵣ, notseg)
                @show sub′, pat′
                m = check_expr_r(sub′, pat′, matches)
                @show m, ind
                if m != ϟ
                    # we found a match, assign the rest to first segment
                    var = varname(first(seg))
                    val = length(ind) < n ?
                        tuple(arg_data[setdiff(1:n, ind)]...) :
                        ()
                    #                        mterm(opₛ, arg_data[setdiff(1:n, ind)])  :
                    #                        missing
                    val′ = get(matches, var, missing)
                    if ismissing(val′)
                        m = MatchDict(m, var, val)
                        return m
                    elseif val == val′
                        return m
                    else
                        # continue the hunt
                    end
                end
            end
    end
    return  ϟ # failed
end

function check_commutative(opₛ, arg_data,
                           opᵣ, arg_rule, matches)
    # commutative checks
    all_matches = []
    for perm_arg_data in permutations(arg_data) # is the same if done on arg_rule right?
        matches_this_perm = ceoaa(perm_arg_data, arg_rule, matches)
        matches_this_perm !== ϟ && push!(all_matches, matches_this_perm)  # return matches_this_perm
    end # else try with next perm
    isempty(all_matches) && return  ϟ
    @show :XXXXC, all_matches
    return first(all_matches)
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
    return maketerm(Expr, operation(rhs), args, nothing)
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
    m = check_expr_r(sub′, pat, MatchDict())

    m == ϟ && return nothing

    r = rewrite(m, last(rule))
    r
end
