
#=
Implement algorithm, through Ch. 3, of of matchpy paper:

Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables by Manuel Krebber

We use expressions to indicate patterns with wildcards specified as:

* `~x`, `~x::pred`
* `~!x`
* `~~x`, `~~x::pred`
* `~~~x`, `~~~x::pred`

* ✓ patterns are expressions might match non-expression
* ✓ defslots should work (could clean up)
* ✓ all wildcard variables need unique `varname`s
* ✓ neim pass -- normalize exponents. Do this normalization only on the pattern side
  that is if opₛ, opₚ = sqrt, ^ then change opₚ = sqrt.
* ✓ assoc/comm + ~x and wrap in function (e.g. ~x + ~a match a + b + c --> (a+b),c, ...
# ✓ ~~x always returns a container of matching arguments (no wrapping is function)
#     write with: :(*(~~x) + *(~β, ~~x)) => :(*(1 + ~β, (~~x)...))
# ✓ ~~~x is 1 or more, ~~x is 0,1 or more
# ✓ goal is rewrite rule to handle :(*(~a, ~~x) + *(~b, ~~x)) => :((~a+~b) * *(~~x...))
# ✓ functions take a container of σs and either reduce (filter) or build upon (product)
#   reduction is like pruning a tree and uses `nothing` value to indicate this;



𝐹 function heads
𝑋 variables: regular, [wild, star, plus]

split symbolic objects into
𝐹₀ 0-arity expressions
𝐿 all symbolic variables
𝑋 wildcard expressions which split into
Xʳᵉᵍᵘˡᵃʳ regular        -- `_is_Wild`
𝑋Xᵖˡᵘˢ   plus variables -- `_is_Plus`
Xˢᵗᵃʳ    star variables -- `_is_Star`


=#
# t matches s if there is a match with σ(t) = s
soperation(f::Any) = Symbol(operation(f))
soperation(f::Symbol) = f

# normalize pattern
# sub  pat  pat′
# sqrt ^    sqrt
#  ^(1//2)  sqrt  ^(1//2)
#  ^(1//3)  cbrt  ^(1//3)
#  ^(-1)     /    ^(-1)
#  e^       exp   e^
#  exp      e^    exp(
#   /       ^(-1) /
function normalize_pattern(pat, sub)
    iscall(sub) || return pat
    opₛ = soperation(sub)
    iscall(pat) || return pat # are there no op examples?
    opₚ = operation(pat)
    if (opₛ, opₚ) == (:sqrt, :^)
        u, v = arguments(pat)
        if eq_expr(v, :(1//2))
            return Expr(:call, :sqrt, u)
        end
    elseif (opₛ, opₚ) == (:cbrt, :^)
        u, v = arguments(pat)
        if eq_expr(v, :(1//3))
            return Expr(:call, :cbrt, u)
        end
    elseif (opₛ, opₚ) == (:^, :sqrt)
        a, b = arguments(sub)
        if unwrap_const(b) == 1//2
            v = only(arguments(pat))
            return Expr(:call, :^, v, Expr(:call, ://, 1,2))
        end
    elseif (opₛ, opₚ) == (:^, :cbrt)
        a, b = arguments(sub)
        if unwrap_const(b) == 1//3
            v = only(arguments(pat))
            return Expr(:call, :^, v, Expr(:call, ://, 1,3))
        end
    elseif (opₛ, opₚ) == (:^, :/)
        a, b = arguments(sub)
        if b == -1
            u, v = arguments(pat)
            if u == 1
                return Expr(:call, :^, v, -1)
            end
        end
    elseif (opₛ, opₚ) == (:^, :exp)
        a, b = arguments(sub)
        if Symbol(unwrap_const(a)) == :ℯ
            v = only(arguments(pat))
            return Expr(:call, :^, ℯ, v)
        end
    elseif (opₛ, opₚ) == (:exp, :^)
        u,v = arguments(pat)
        if u == ℯ
            return Expr(:call, :exp, v)
        end
    elseif (opₛ, opₚ) == (:/, :^)
        u,v = arguments(pat)
        if eq_expr(v, :(-1))
            return Expr(:call, :/, 1, u)
        end
    end
    return pat
end


# θ \theta  is an iterator of substitutions;
# default is (match_dict(),)
function match_one_to_one(ss, p, fₐ = nothing, θ = (match_dict(),))
    ## @show :m11, ss, p, fₐ
    n = length(ss)
    if !has_𝑋(p)     # constant symbol
        # match if p == ss(1)
        n == 1 && eq_expr(only(ss), p) && return θ
        return ∅
    elseif is_slot_or_defslot(p) && isnothing(fₐ)  # regular variable
        if n == 1
            s₁ = only(ss)
            var = varname(p)
            σ′ = match_dict(var => s₁)

            has_predicate(p) && !_evalguard(get_predicate(p), s₁) && return ∅

            return union_merge(θ, σ′)
        end
    elseif iscall(p) && any(has_defslot, arguments(p))
        return clear_defslots(ss, p, fₐ, θ)
    elseif is_𝑋(p)                      # sequence variable?
        var = varname(p)
        value = is_slot_or_defslot(p) && !isnothing(fₐ) ? sterm(fₐ, ss) : ss
        has_predicate(p) && !_evalguard(get_predicate(p), value) && return ∅
        σ′ = match_dict(var => value)

        if is_segment(p) || n ≥ 1
            return union_merge(θ, σ′)
        end

    elseif n == 1
        s = only(ss)
        iscall(s) || return ∅ # p is non constant, so must be compound, s should be as well

        p = normalize_pattern(p,s)
        opₛ = operation(s)
        𝑜𝑝ₛ = Symbol(opₛ)
        if operation(p) == 𝑜𝑝ₛ
            ss, ps = arguments(s), arguments(p)
            fₐ′ = isassociative(opₛ) ? opₛ : nothing
            λ = iscommutative(fₐ′) ? match_commutative_sequence : match_sequence
            return λ(ss, ps, fₐ′, θ)
        end

    end
    return ∅
end


function clear_defslots(ss, p, fₐ, θ)
    inds = findall(has_defslot, arguments(p))
    opₚ = operation(p)
    ps = arguments(p)

    θ′′ = MatchDict[]
    for inds′ = powerset(1:length(inds))
        # we use default for inds′, nondefault for others
        ps′ = copy(ps)
        σ′ = match_dict()
        for j ∈ inds′
            i′ = inds[j]
            pᵢ = ps[i′]
            # p is ~!x or (a)^(~!x)
            if is_defslot(pᵢ)
                ps′ = vcat(ps′[1:i′-1], ps′[i′+1:end])
                defval = defslot_op_map[opₚ]
                σ′ = match_dict(σ′, varname(pᵢ) => defval)
            else
                # power
                a, b = arguments(pᵢ)
                ps′ = vcat(ps′[1:i′-1], a, ps′[i′+1:end])
                defval = defslot_op_map[:^]
                σ′ = match_dict(σ′, varname(b) => defval)
            end
        end
        # replace defslot with slot
        for j in setdiff(eachindex(inds), inds′)
            i′ = inds[j]
            pᵢ = ps[i′]
            if is_defslot(pᵢ)
                pᵢ′ = :(~$(varname(pᵢ)))
            else
                a, b = arguments(pᵢ)
                pᵢ′ = Expr(:call, :^, a, :(~$(varname(b))))
            end
            # replace in ps′ which may be shorter than ps
            i = findall(==(pᵢ), ps′)
            ps′[i] .= (pᵢ′,)
        end

        p′ = pterm(operation(p), ps′)
        θ′ = (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
        itr = match_one_to_one(ss, p′, fₐ, θ′)
        (isempty(itr) || isnothing(itr)) && continue
        #@show inds′, collect(itr)
        isempty(inds′) && return itr # defslot not needed
        θ′′ = union(θ′′, itr)
    end

    return θ′′

end

# 3.3 match non-commutative function
#     return iterator of matches
function match_sequence(ss, ps, fₐ=nothing, θ=(match_dict(),))
    #@show :ms, ss, ps, collect(θ)
    n, m = length(ss), length(ps)
    nstar = count(is_segment, ps)
    m - nstar > n && return ∅ # total number of arguments required in the pattern
                              # exceeds the number of arguments in the subject.

    nplus = count(is_plus, ps)
    if !isnothing(fₐ)
        nplus += count(is_slot, ps) # ount regular vars as plus vars in assoc. function
    end

    if iszero(nstar) && iszero(nplus) && n == m
        for (s,p) ∈ zip(ss, ps)
            θ = match_one_to_one([s], p, fₐ, θ)
        end
        return θ

    end

    nfree = n - m + nstar
    nseq = nstar + nplus
    λ = ks -> begin
        #(!isempty(ks) && sum(ks) != nfree) && return nothing
        i, j = 1, 1 # 0,0 in 0-based
        θ′ = θ
        for (l, pl) ∈ enumerate(ps)
            lsub = 1
            if (is_plus(pl) || is_segment(pl)) ||
                (is_slot(pl) && !isnothing(fₐ))
                kj = isempty(ks) ? 1 : ks[j]
                lsub = lsub + kj
                if is_segment(pl)
                    lsub = lsub - 1
                end
                j = j + 1
            end
            ss′ = ss[i:(i+lsub-1)] # si...si+lsub (note -1 here)
            θ′ = match_one_to_one(ss′, pl, fₐ, θ′)
            θ′ == ∅  && break
            i = i + lsub
        end
        θ′ == ∅ && return nothing
        return θ′
    end
   i = multiexponents(nseq, nfree) # For every distribution of free arguments is ss among the
                                    # seq. vars...
    ii = Iterators.map(λ, i)
    iii = Iterators.filter(!isnothing, ii)
    Iterators.flatten(iii)
end

## ---- commutative (associative when fₐ != nothing)

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (match_dict(),))
    #@show :mcs, ss, ps, collect(θ)
    out = _match_constant_patterns(ss, ps)
    isnothing(out) && return ∅

    ss, ps = out

    ## chain togetther
    i = let ss=ss, ps=ps
        Iterators.map(σ -> (ss, ps, σ), θ)
    end

    ii = Iterators.map(enumerate(i)) do (j,a)
        ss, ps, σ = a
        itr = _match_defslot_patterns(ss, ps, fₐ, σ)
    end

    iia = Iterators.flatten(ii)

    iii = Iterators.map(iia) do a
        ss, ps, σ = a
        itr = _match_non_variable_patterns(ss, ps, fₐ, σ)
        itr
    end

    iiia = Iterators.filter(!isnothing, iii)
    iiib = Iterators.flatten(iiia)


    iv = Iterators.map(iiib) do a
        ss, ps, σ = a
        itr = _match_regular_variables(ss, ps, fₐ, σ)
        itr
    end

    iva = Iterators.flatten(iv)
    ivb = Iterators.filter(!isnothing, iva)

    v = Iterators.map(ivb) do a
        ss, ps, σ = a
        itr = _match_sequence_variables(ss, ps, fₐ, σ)
    end

    va = Iterators.filter(!isnothing, v)
    vb = Iterators.flatten(va)
    vb

end

# return trimmed ss, ps or nothing
function _match_constant_patterns(ss, ps)
    # @show :mcp, ss, ps
    Pconst = filter(!has_𝑋, ps)
    ss′ = ss
    for p ∈ Pconst
        p in ss′ || return nothing
        ss′ = filter(!=(p), ss′)
    end
    ps′ = filter(p -> p ∉ Pconst, ps)
    return (ss′, ps′)
end


# match defslotpatterns early
# return iterator of (ss, ps, σ) values
function _match_defslot_patterns(ss, ps, fₐ=nothing, σ=match_dict())
    #@show :mds, ss, ps, fₐ

    inds = findall(has_defslot, ps)

    isempty(inds) && return ((ss, ps, σ),)
    θ = Any[]

    ## we just create matching trees with all possible choices of
    ## defslots being slots or their defaults and let the algorithm trim
    ## them down.

    for inds′ = powerset(1:length(inds)) # |inds| slot variables
        # we use default for inds′, nondefault for others
        σ′ = match_dict()
        ps′ = copy(ps)

        # use default here; trim ps′, set σ′
        for j ∈ inds′
            i′ = inds[j]
            pᵢ = ps[i′]
            if is_defslot(pᵢ)
                ps′ = vcat(ps′[1:i′-1], ps′[i′+1:end])
                σ′ = match_dict(σ′, :defslot=>true,
                                varname(pᵢ) => defslot_op_map[Symbol(fₐ)])
            else # power
                a, b = arguments(pᵢ)
                ps′ = vcat(ps′[1:i′-1], a, ps′[i′+1:end])
                σ′ = match_dict(σ′, :defslot => true,
                                varname(b) => defslot_op_map[:^])
            end
        end

        # replace defslot with slot
        for j in setdiff(eachindex(inds), inds′)
            i′ = inds[j]
            pᵢ = ps[i′]
            if is_defslot(pᵢ)
                pᵢ′ = :(~$(varname(pᵢ)))
            else
                a, b = arguments(pᵢ)
                pᵢ′ = Expr(:call, :^, a, :(~$(varname(b))))
            end
            k = findall(==(pᵢ), ps′)
            ps′[k] .= (pᵢ′,)
        end

        # if compatible, add
        if iscompatible(σ, σ′)
            push!(θ, (ss, ps′, merge_match(σ, σ′)))
        end
    end
    return θ
end

# trims down ss, ps
# returns (ss,ps) or nothing
function  _match_matched_variables(ss, ps, σ)
    #@show :mmv, ss, ps, σ

    # subtract from, ps, ss previously matched variables
    (isnothing(σ) || isempty(σ)) && return (ss, ps)
    ps′, psₒ = _groupby(is_𝑋, ps)
    ps′′ = varname.(ps′)
    for (p,s) ∈ σ
        ind = findall(==(p), ps′′)
        for i ∈ ind
            v = ps′[i]
            itr = (is_slot(v) || is_defslot(v)) ? (s,) : s
            for sᵢ ∈ itr
                j = findfirst(==(sᵢ), ss)
                isnothing(j) && return nothing
                ss = vcat(ss[1:(j-1)], ss[(j+1):end])
            end
        end
    end

    ps = vcat(psₒ, [v for v in ps′ if varname(v) ∉ keys(σ)])
    ss, ps

end

# match non_variable_patterns
# return iterator of (ss, ps, σ) or nothing
function _match_non_variable_patterns(ss, ps, fc=nothing, σ=match_dict())
    #@show :mnvp, ss, ps, σ

    out = _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing
    ss, ps = out
    ps′, ps′′ = _groupby(!is_𝑋, ps)

    n = length(ps′)
    n == 0 && return ((ss, ps, σ), )
    n ≤ length(ss) || return nothing

    i = permutations(1:length(ss), n)
    f = inds -> begin
        ss′= ss[inds]
        θ′ = (σ,)
        for (s,p) ∈ zip(ss′, ps′)
            p, θ′ = check_nonmatching_defslot(s,p, θ′)
            p = normalize_pattern(p,s) # rewrite pattern if needed
            (iscall(s) && iscall(p)) || return nothing
            soperation(s) == operation(p) || return nothing
            fₐ′ = isassociative(operation(s)) ? operation(s) : nothing
            λ = iscommutative(fₐ′) ? match_commutative_sequence : match_sequence
            θ′ = λ(arguments(s), arguments(p), fₐ′, θ′)
            θ′ == ∅ && return nothing
        end
        θ′ == ∅ && return nothing
        ss′′ = setdiff(ss, ss′) # so ss′ and ps′ have matches in θ′
        return ((ss′′, ps′′, σ) for σ ∈ θ′)
    end
    ii = Iterators.map(f, i)
    iii = Iterators.filter(!isnothing, ii)
    iv = Iterators.flatten(iii)
end

# does p have a defslot that doesn't match at the operation level, then try and fix
# before the operations don't match
function check_nonmatching_defslot(s, p, θ′)
    #@show :cnd, s, p
    if iscall(p)
        opₚ = operation(p)
        if (!iscall(s) || (Symbol(operation(s)) != opₚ))
            if opₚ ∈ (:+, :*)
                argsₚ = arguments(p)
                inds = findall(is_defslot, argsₚ)
                if !isempty(inds)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict((varname.(argsₚ[inds]) .=> val)...)
                    θ′ = (merge_match(σ, σ′) for σ ∈ θ′ if iscompatible(σ, σ′))

                    ps = argsₚ[setdiff(eachindex(argsₚ), inds)]
                    p′ = pterm(opₚ, ps)
                    return p′, θ′
                end
            elseif opₚ == :^
                a,b = arguments(p)
                if is_defslot(b)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict(varname(b) => val)
                    θ′ = (merge_match(σ, σ′) for σ ∈ θ′)
                    p′ = a
                    return p′, θ′
                end
            end
        end
    end
    return p, θ′
end


# match ~x type variables
# return iterator of (ss, ps, σ)
function _match_regular_variables(ss, ps, fc=nothing, σ = match_dict())
    #@show :mrv, ss, ps, fc, σ
    isempty(ps) && !isempty(ss) && return ∅
    isempty(ss) && !isempty(ps) && return ∅

    isempty(ps) && return ((ss, ps, σ),)
    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return ∅

    ss, ps = out

    # fₐ is  commutative, maybe associative
    isassociative(fc) && return ((ss, ps, σ),) # associative turns ~x into ~~x


    ps_reg, ps′′ = _groupby(is_slot, ps)
    isempty(ps_reg) && return ((ss, ps, σ),)

    if length(ps_reg) < length(ss)
        if ps_reg == ps
            # can't match, not enough
            return nothing # ∅
        end
    end

    dp = _countmap(ps_reg)
    ds = _countmap(ss)
    i = _split_take(ds, dp)

    ii = Iterators.filter(ab -> begin
                          iscompatible(first(ab), σ)
                          end, i)

    iii = Iterators.map(ii) do (σ′, ds)
        σ′ = merge_match(σ, σ′)
        ss′′ = _uncountmap(ds)
        (ss′′, ps′′, σ′)
    end

    return iii
end


# return iterator of matches, σ
function _match_sequence_variables(ss, ps, fc=nothing, σ = match_dict())
    #@show :msv, ss, ps, fc, σ

    isempty(ps) && !isempty(ss) && return ∅
    isempty(ss) && !isempty(ps) && return ∅

    isempty(ps) && return (σ, )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    ss, ps = out

    if !isassociative(fc)
        !isempty(filter(is_slot, ps)) && return nothing #()
    end

    vs, vs′ = _groupby(x -> is_slot(x) || is_plus(x), ps)

    length(vs) > length(ss) && return nothing #(); too many plus variables

    ds = _countmap(ss)
    dplus, dstar = _countmap(vs), _countmap(vs′)

    vars = vcat(first.(dplus), first.(dstar))
    isempty(vars) && return nothing #()

    svars = first.(ds)

    pluses = last.(dplus)
    stars = last.(dstar)
    ks = vcat(pluses, stars)

    n1, n2 = length(pluses), length(stars)
    n = n1 + n2

    h = isnothing(fc) ? identity :
        (as) -> pterm(fc, as)

    # rename
    ssᵥ = [v for (k,v) in ds] # last.(ds)
    i = ntuple(zero, Val(n))


    ii = Iterators.filter(Iterators.product(
        (Iterators.product((0:s for _ in 1:n)...) for s in ssᵥ)...)) do u
            all(sum(ui .* ks) == si for (ui,si) in zip(u, ssᵥ)) &&
                all(sum(ui[i] for ui in u) > 0 for i in 1:n1)
        end

    iii = Iterators.map(Iterators.reverse(ii)) do u
        σ′ = σ
        for (j, v) ∈ enumerate(vars)
            vv = []
            for (i,s) in enumerate(svars)
                for _ in 1:u[i][j]
                    push!(vv, s) # allocates less than appending repeat([s],uᵢⱼ)
                end
            end
            # give defaults; missing or value
            if isempty(vv)
                if is_defslot(v)
                    vv′ = defslot_op_map[fc]
                elseif is_segment(v)
                    vv′ = Any[] #()
                else
                    vv′ = nothing
                end
            else
                # if var is ~x fc not nothing
                vv = sort(vv, lt = <ₑ)
                vv′ = (is_slot(v) && !isa(fc, Nothing)) ? sterm(fc, vv) : vv
            end
            if !isnothing(vv′)
                var = varname(v)
                if has_predicate(v)
                    pred = get_predicate(v)
                    if _evalguard(pred, vv′)
                        σ′′ = match_dict(var => vv′)
                    else
                        return nothing
                    end
                else
                    σ′′ = match_dict(var => vv′)
                end
                iscompatible(σ′, σ′′) || return nothing
                σ′ = merge_match(σ′, σ′′)
            end
        end
        iscompatible(σ, σ′) || return nothing
        return merge_match(σ, σ′)
    end

    iv = Iterators.filter(!isnothing, iii)
    iv
end

# counting functions
function _countmap(x)
    d = Dict()
    [(d[xi] = get(d, xi, 0) + 1) for xi in x]
    return [k => v for (k,v) ∈ d]
end
function _uncountmap(dx)
    return vcat((repeat([k],v) for (k,v) in dx)...)
end

# different ways to grab the pie
function _split_take(ds, dp)
    n = length(ds)
    k = length(dp)

    i = Iterators.product((1:n for _ in 1:k)...)
    ii = Iterators.map(i) do inds
        ds′ = copy(ds)
        σ = ∅
        for (i, (p, np)) ∈ zip(inds, (dp))
            s, ns = ds′[i]
            np > ns && (σ = ∅; break) # won't fit
            ds′[i] = s => (ns - np)
            σ = merge_match(σ, match_dict(varname(p) => s)) # XXX? Check compatible?
        end
        σ == ∅ && return nothing
        (σ, ds′)
    end
    iii = Iterators.filter(!isnothing, ii)
end
