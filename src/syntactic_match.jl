module SyntacticMatch

using TermInterface
include("utils.jl")

function syntactic_match(s, p, σ = match_dict())

    if !has_𝑋(p) # no wild
        return as_symbol_or_literal(s) == p ? σ : ϟ
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




end
