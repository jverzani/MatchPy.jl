function syntactic_match(s, p, σ = match_dict())
    if !has_𝑋(p) # no wild
        out = (_unwrap_const(s) == _unwrap_const(p)) ? σ : nothing
        return out
    elseif is_slot(p)
        var = varname(p)
        if haskey(σ, var)
            σ[var] != s && return ϟ
            return σ
        end

        if has_predicate(p)
            pred = get_predicate(p)
            if !Base.invokelatest(eval(pred), s)
                return ϟ
            end
        end
        ##_@show var, s
        σ′ = match_dict(σ, var => s)
        return σ′

    end

    iscall(p) || return σ

    # deal with default slots
    if !iscall(s) || (iscall(s) && Symbol(operation(s)) != operation(p)) &&
        any(_is_DefSlot, arguments(p)) &&
        operation(p) ∈ keys(defslot_op_map)
        # try without
        # clean this up!
        σ′ = FAIL_DICT
        ##_@show :defslot_use
        if operation(p) ∈ (:*, :+)
            as, p′′ = _groupby(!is_defslot, arguments(p))
            p′ = only(p′′) # must be just one slot variable
            𝑝 = length(as) == 1 ? only(as) : Expr(:call, operation(p), as...)
            σ′ = syntactic_match(s, 𝑝, σ)
        elseif operation(p) == :^
            a, p′ = arguments(p)
            is_defslot(p′) || error("Def Slot is exponent in a power")
            σ′ = syntactic_match(s, a, σ)
        end
        if iscompatible(σ, σ′)
            σ′ = match_dict(σ′, p′ => defslot_op_map[operation(p)])
            return merge_match(σ, σ′)
        end
    end

    iscall(s)  || return σ
    f, f′ = Symbol(operation(s)), operation(p)
    f == f′ || return ϟ

    n, n′ = length(arguments(s)), length(arguments(p))
    n == n′ || return ϟ

    for (sᵢ, pᵢ) ∈ zip(arguments(s), arguments(p))
        σ′ = syntactic_match(sᵢ, pᵢ, σ)
        σ′ == ϟ && return ϟ
        !iscompatible(σ, σ′) && return ϟ
        σ = merge_match(σ, σ′)
    end

    return σ
end

# other matching
## Matching
# copy of  CallableExpressions.expression_map_matched(pred, mapping, u)
# if argument, `a`, matches via `is_match` replace with `f(a)`
function map_matched(ex, is_match, f)
    T = symtype(ex)
    if !iscall(ex)
        return is_match(ex) ? f(ex) : ex
    else
        is_match(ex) && return f(ex)
        iscall(ex) || return ex
        children = map_matched.(arguments(ex), is_match, f)
        return sterm(T, operation(ex), children)
    end
end


# does predicate match an argument in the expression
function _ismatch(ex, pred)
    if iscall(ex)
        return any(Base.Fix2(_ismatch, pred), arguments(ex))
    elseif isexpr(ex)
        return any(Base.Fix2(_ismatch, pred), children(ex))
    end
    pred(ex)
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

# does predicate match an operation in the expression
function _ismatchhead(ex, pred)
    if iscall(ex)
        pred(operation(ex)) && return true
        return any(Base.Fix2(_ismatchhead, pred), arguments(ex))
    elseif isexpr(ex)
        pred(head(ex)) && return true
        return any(Base.Fix2(_ismatchhead, pred), children(ex))
    end
    pred(ex)
end
