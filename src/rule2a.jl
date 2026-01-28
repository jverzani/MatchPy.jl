# This is derived from https://github.com/JuliaSymbolics/SymbolicIntegration.jl/tree/main/src/methods/rule_based/rule2.jl
# Licensed under MIT with Copyright (c) 2022 Harald Hofstätter, Mattia Micheletta Merlin, Chris Rackauckas, and other contributors
function _eval(pred, data)
    out = try
        Base.invokelatest(eval(pred), ϟ(data))
    catch err
        false
    end
    out
end


# TODO matches does assignment or mutation? which is faster?
# TODO ~a*(~b*~c) currently will not match a*b*c . a fix is possible
# TODO rules with symbols like ~b * a currently cause error

# for when the rule contains a symbol, like ℯ, or a literal number
function check_expr_r(data, rule::Union{Real, Symbol}, σs)
    isequal(rule, ϟ(data)) && return σs
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

    # if there is a segment in the (only) argument
    if (iscall(rule) &&
        length(arguments(rule)) == 1 &&
        is_segment(first(arguments(rule))))
        return only_argument_is_segment(data, rule, σs)
    end

    # rule is a normal call, check operation and arguments
    if (operation(rule) == ://) && _is_rational(data)
        return  has_rational(data, rule, σs)
    end

    !iscall(data) && return MatchDict[]

    opᵣ, 𝑜𝑝ₛ = operation(rule), operation(data)
    # check opᵣ for special case
    if opᵣ ∈ (:^, :sqrt, :exp)
        return different_powers(data, rule, σs)
    end

    # gimmick to make Neim work in some cases:
    # * if data is a division transform it to a multiplication
    # (the final solution would be remove divisions form rules)
    # * if the rule is a product, at least one of the factors is a power, and data is a division
    neim_pass, arg_data, arg_rule = neim_rewrite(data, rule)
    Symbol(𝑜𝑝ₛ) != opᵣ && !neim_pass && return MatchDict[]

    # segments variables means number of arguments might not match
    if (any(is_segment, arg_rule))
        return has_any_segment(𝑜𝑝ₛ, arg_data, opᵣ, arg_rule,  σs)
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

# expression has defslot
function has_defslot(i, data, rule, σs)
    ps = copy(arguments(rule))
    pᵢ = ps[i]
    qᵢ = :(~$(pᵢ.args[2].args[2]))
    ps[i] = qᵢ

    # build rule expr without defslot and check it
    newr = Expr(:call, operation(rule), ps...) # not pterm here!
    σ′s = check_expr_r(data, newr, σs)
    !isempty(σ′s) && return σ′s # had a match

    # if no normal match, check only the non-defslot part of the rule
    deleteat!(ps, i)
    tmp = pterm(operation(rule), ps)
    σs = check_expr_r(data, tmp, σs)

    var = varname(qᵢ)
    value = get(defslot_op_map, operation(rule), -1)
    return [match_dict(σ, var => value) for σ ∈ σs if σ != FAIL_DICT]

end

function only_argument_is_segment(data, rule, σs)
    !iscall(data) && return MatchDict[]
    opₛ, opᵣ = Symbol(operation(data)), operation(rule)
    opₛ == opᵣ || return MatchDict[]

    # return the whole data (not only vector of arguments as in rule1)
    σ′ = match_dict(varname(only(arguments(rule))) => arguments(data))
    collect(union_merge(σs, σ′))
end

function has_rational(data, rule, σs)
    # rational is a special case, in the integration rules is present only in between numbers, like 1//2

    as = arguments(rule)
    data.num == first(as) && data.den == last(as) && return σs
    # r.num == rule.args[2] && r.den == rule.args[3] && return matches::MatchDict
    return MatchDict[]
end

# make powers equivalent for checking
# e.g. sqrt(x) --> x^(1//2)
function different_powers(data, rule, σs)
    arg_data = arguments(data)
    arg_rule = arguments(rule)
    opᵣ, opₛ = operation(rule), Symbol(operation(data))

    b = first(arg_data)

    if opᵣ === :^

        # try first normal checks
        if (opₛ === :^)
            σ′s = ceoaa(arg_data, arg_rule, σs)
            !isempty(σ′s) && return σ′s
        end


        # try building frankestein arg_data (fad)
        fad = []
        is1divsmth = (opₛ == :/) && _isone(first(arg_data))

        if is1divsmth && iscall(arg_data[2]) && (Symbol(operation(arg_data[2])) == :^)

            # if data is of the alternative form 1/(...)^(...)
            m = arg_data[2]
            push!(fad, arguments(m)[1], -1*arguments(m)[2])

        elseif is1divsmth && iscall(arg_data[2]) && (Symbol(operation(arg_data[2])) == :sqrt)

            # if data is of the alternative form 1/sqrt(...),
            # it might match with exponent -1//2
            m = arg_data[2] # like b^m
            push!(fad, arguments(m)[1], -1//2)

        elseif is1divsmth && iscall(arg_data[2]) &&
            (Symbol(operation(arg_data[2])) === :exp)
            # if data is of the alternative form 1/exp(...),
            # it might match ℯ ^ -...
            m = arg_data[2] # like b^m
            pow = first(arguments(m))

            push!(fad, ℯ, sterm(typeof(pow), -, (pow,))) #-1*arguments(m)[1])

        elseif is1divsmth
            # if data is of the alternative form 1/(...),
            # it might match with exponent = -1
            m = arg_data[2] # like b^m
            push!(fad, m, -1)

        elseif (opₛ  === :^) && iscall(b) &&
            (Symbol(operation(b)) === :/) &&
            _isone(arguments(b)[1])

            # if data is of the alternative form (1/...)^(...)
            m = arg_data[2] # like b^m
            push!(fad, arguments(b)[2], -1*m)

        elseif opₛ === :exp
            # if data is a exp call, it might match with base e
            push!(fad, ℯ, b)

        elseif opₛ === :sqrt
            # if data is a sqrt call, it might match with exponent 1//2
            push!(fad, b, 1//2)

        else
            return MatchDict[]

        end

        return ceoaa(fad, arg_rule, σs)

    elseif opᵣ === :sqrt
        if (opₛ === :sqrt)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (ϟ(arg_data[2]) == :(1//2)) #1//2)
            tocheck = (b,)
        else
            return MatchDict[]
        end

        return ceoaa(tocheck, arg_rule, σs)

    elseif opᵣ === :exp
        if (opₛ === :exp)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (ϟ(b) == :ℯ)
            m = arg_data[2]
            tocheck = (m,)
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
    if (opᵣ === :*) && opₛ === :/ && any(is_operation(:^), arg_rule)
        #x->(isa(x,Expr) && x.head===:call && x.args[1]===:^), arg_rule) && (operation(data)===/)

        neim_pass = true

        n = arg_data[1]
        d = arg_data[2]
        # then push the denominator of data up with negative power
        sostituto = []
        if iscall(d) && opₛ == :^ #(operation(d)==^)

            a, b, c... =  arg_data
            val = sterm(typeof(a), ^, (a,b))
            push!(sostituto, val)

        elseif iscall(d) && opₛ == :*
            # push!(sostituto, map(x->x^-1,arguments(d))...)
            for factor in arguments(d)
                val = sterm(typeof(factor), ^, (factor, -1))
                push!(sostituto, val)
            end
        elseif iscall(d) && soperation(d) == :^
            a,b = arguments(d)
            m = sterm(typeof(d), -, (b,))
            val = sterm(typeof(d), ^, (a, m))
            push!(sostituto, val)
        else
            val = sterm(typeof(d), ^, (d, -1))
            push!(sostituto, val)
        end

        new_arg_data = []

        if iscall(n)
            if Symbol(operation(n)) === :*
                append!(new_arg_data, arguments(n))
            else
                push!(new_arg_data, n)
            end
        elseif !_isone(n)
            push!(new_arg_data, n)
            # else dont push anything bc *1 gets canceled
        end

        append!(new_arg_data, sostituto)

        arg_data = new_arg_data

        # printdb(4,"Applying neim trick, new arg_data is $arg_data")
    end

    return (neim_pass, arg_data, arg_rule)

end

function has_any_segment(𝑜𝑝ₛ, arg_data,
                         opᵣ, arg_rule, σs)

    seg, notseg = _groupby(is_segment, arg_rule)
    n,m = length(arg_data), length(notseg)
    if m > n
        return MatchDict[]
    elseif m == 0
        # assign all to the first!
        σ′s = MatchDict[]

        var′, vars... = seg
        var = varname(var′)
        val = tuple(arg_data...) #Expr(:call, opₛ, arg_data...)
        for σ ∈ σs
            val′ = get(σ, var, missing)
            if ismissing(val′)
                σ′ = match_dict(σ, var => val)
                for v ∈ varname.(vars)
                    σ′ = match_dict(σ′, v => ())
                end
                push!(σ′s,σ′)
            elseif val == val′
                push!(σ′s,σ)
            end
        end# XXX?
        return σ′s
    elseif 0 < m ≤ n
        σ′′s = MatchDict[]

        for ind ∈ combinations(1:n, m)
            # take m of the values and match
            sub′ = sterm(typeof(first(arg_data)), 𝑜𝑝ₛ, arg_data[ind])
            pat′ = pterm(opᵣ, notseg) # can be an issue!
            for σ ∈ σs
                σ′s = check_expr_r(sub′, pat′, [σ])
                if !isempty(σ′s)
                    # we found a match, assign the rest to first segment
                    for σ′ ∈ σ′s
                        v = first(seg)
                        var = varname(v)
                        val = length(ind) < n ?
                            tuple(arg_data[setdiff(1:n, ind)]...) :
                            ()
                        val′ = get(σ′, var, missing)
                        if ismissing(val′)
                            if !has_predicate(v) ||
                                (has_predicate(v) && _eval(get_predicate(v), val) )
                                σ′ = match_dict(σ′, var=>val)
                                push!(σ′′s, σ′)
                            end
                        elseif val == val′
                            push!(σ′′s, σ)
                        else
                            # continue the hunt
                        end
                    end
                end
            end
        end
        if length(seg) > 0
            # match all segments with (), then match the rest
            σ′′′ = match_dict()
            for v ∈ seg
                σ′′′ = match_dict(σ′′′, varname(v) => ())
            end
            σ′′′s = union_merge(σs, σ′′′)
            sub′ = sterm(typeof(first(arg_data)), 𝑜𝑝ₛ, arg_data)
            pat′ = pterm(opᵣ, notseg)
            σ′′′s = check_expr_r(sub′, pat′, σ′′′s)
            !isempty(σ′′′s) && append!(σ′′s, σ′′′s)
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
