#= ----- TODO ----
* ✓ patterns are expressions might match non-expression
* ✓ neim pass -- normalize exponents. Do this normalization only on the pattern side
  that is if opₛ, opₚ = sqrt, ^ then change opₚ = sqrt.
* ✓ assoc/comm + ~x and wrap in function (e.g. ~x + ~a match a + b + c --> (a+b),c, ...
# ✓ ~~x always returns a container of matching arguments (no wrapping is function)
#     write with: :(*(~~x) + *(~β, ~~x)) => :(*(1 + ~β, (~~x)...))
# ✓ ~~~x is 1 or more, ~~x is 0,1 or more
# ✓ goal is rewrite rule to handle :(*(~a, ~~x) + *(~b, ~~x)) => :((~a+~b) * *(~~x...))
# functions take a container of σs and either reduce (filter) or build opon (product)
#   reduction is like pruning a tree and uses `nothing` value to indicate this;
=#
# implement algorithm of matchpy paper through Ch. 3
# from SimpleExpressions but modified to work with expressions for patterns

# Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables by Manuel Krebber

# add in SymbolicUtils
# * defslots -- A DefSlot variable is written as ~!x. Works like a normal slot, but can also take default values if not present in the expression.
# * segment -- Star variables (0, 1 or more)
# * add guards

# 𝐹 function heads
# 𝑋 variables: regular, [wild, star, plus]

# split symbolic objects into
# 𝐹₀ 0-arity expressions
# 𝐿 all symbolic variables
# 𝑋 wildcard expressions which split into
# Xʳᵉᵍᵘˡᵃʳ regular        -- `_is_Wild`
# 𝑋Xᵖˡᵘˢ   plus variables -- `_is_Plus`
# Xˢᵗᵃʳ    star variables -- `_is_Star`

# clean up iterators
# we use nothing to terminate a branch, flatten to branch
clean(itr) = Iterators.filter(!isnothing, Iterators.flatten(itr))
#    Iterators.flatten(Iterators.filter(!isnothing, itr))

# t matches s if there is a match with σ(t) = s
soperation(f::Any) = Symbol(operation(f))

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
    #@show :m11, ss, p, fₐ
    n = length(ss)
    if !has_𝑋(p)     # constant symbol
        # match if p == ss(1)
        n == 1 && eq_expr(only(ss), p) && return θ
        return ∅
    elseif is_slot_or_defslot(p) && isnothing(fₐ)  # regular variable
        if n == 1
            data = only(ss)
            σ′ = match_dict()
            var = varname(p)
            if has_predicate(p)
                pred = get_predicate(p)
                if _evalguard(pred, data)
                    σ′ = match_dict(σ′, var => data)
                else
                    return ∅
                end
            else
                ##_@show var,data
                σ′ = match_dict(σ′, var => data)
            end
            return union_merge(θ, σ′)
        end

    elseif is_𝑋(p)                      # sequence variable?
        var = varname(p)
        if has_predicate(p) &&
            _evalguard(get_predicate(p), ss)
            return ∅
        end

        if is_slot_or_defslot(p) && !isnothing(fₐ) # regular and associative function
            value = pterm(Symbol(fₐ), ss)
            σ′ = match_dict(var => value)
        else
            σ′ = match_dict(var => ss)
        end
        if is_segment(p) || n ≥ 1
            return union_merge(θ, σ′)
        end

    elseif n == 1
        s = only(ss)
        iscall(p) || return ∅

        asₚ = copy(arguments(p))

        if any(is_defslot, asₚ)
           ## @show :defslot
            # Defslots -- first check if there is a match with a slot variable
            # if so, return that. Else, replace with default value and move on.

            i = findfirst(is_defslot, asₚ)
            pᵢ = asₚ[i]
            qᵢ = :(~$(pᵢ.args[2].args[2]))
            asₚ[i] = qᵢ

            dvar = varname(pᵢ)

            𝑝 = pterm(operation(p), asₚ)
            θ′ = match_one_to_one(ss, 𝑝, fₐ, θ)
            if !isempty(θ′)
                return θ′
            else
                opₚ = operation(p)
                θ = (match_dict(σ′, dvar => defslot_op_map[opₚ]) for σ′ ∈ θ)
                # replace pieces of `p`
                if opₚ ∈ (:(+), :(*))
                    bs = [asₚ[j] for j in 1:length(asₚ) if j != i]
                    p = pterm(opₚ, bs)
                elseif opₚ == :(^)
                    p = asₚ[1]
                end
            end

            return match_one_to_one(ss, p, fₐ, θ)

        end
        iscall(s) || return ∅ # ??

        p = normalize_pattern(p,s) # rewrite operations
        if operation(p) == soperation(s)
            ps, qs = arguments(p), arguments(s)
            fₐ′ = isassociative(operation(s)) ? operation(s) : nothing
            λ = iscommutative(fₐ′) ? match_commutative_sequence : match_sequence
            return λ(qs, ps, fₐ′, θ)
        end

    end
    return ∅
end

# 3.3 match non-commutative function
#     return iterator of matches
function match_sequence(ss, ps, fₐ=nothing, θ=(match_dict(),))
    n, m = length(ss), length(ps)
    nstar = count(is_segment, ps)

    m - nstar > n && return ∅
    nplus = count(is_plus, ps)

    if !isnothing(fₐ)
        nplus += count(is_slot, ps)
    end
    m < n && iszero(nstar) && iszero(nplus) && return ∅

    # XXX check for non-variables match, if so return ()
    if nstar + nplus == 0 && !any(has_𝑋, ps)
        # no wildcards, do we match?
        length(ss) == length(ps) || return ∅
        all(eq_expr(s,p) for (s,p) ∈ zip(ss, ps)) && return θ
        return ∅
    end

    nfree = n - m + nstar
    nseq = nstar + nplus
    λ = ks -> begin
        #(!isempty(ks) && sum(ks) != nfree) && return nothing
        i, j = 1, 1 # 0,0??
        θ′ = θ
        for (l,pl) ∈ enumerate(ps)
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

            ss′ = ss[i:(i+lsub-1)] # note -1 here
            θ′ = match_one_to_one(ss′, pl, fₐ, θ′)
            θ′ == ∅  && break
            i = i + lsub
        end
        θ′ == ∅ && return nothing
        return θ′
    end
    i = multiexponents(nseq, nfree)
    ii = Iterators.map(λ, i)
    iii = clean(ii)
    return iii
end

## ---- commutative (associative when fₐ != nothing)

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (match_dict(),))
    ##@show :mcs, ss, ps, fₐ
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
        itr = clean(itr)
    end

    iii = Iterators.map(ii) do a
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

    va = Iterators.flatten(v)
    Iterators.filter(!isnothing, va)

end

# return trimmed ss, ps or nothing
function _match_constant_patterns(ss, ps)
   ## @show :mcp, ss, ps
    Pconst = filter(!has_𝑋, ps)
    for p ∈ Pconst
        inds = Int[]
        for (i,sᵢ) ∈ enumerate(ss) # ss′
            eq_expr(sᵢ, p) && push!(inds, i)
        end
        isempty(inds) && return nothing
        ss = ss[setdiff(1:length(ss), inds)]
    end

    ps′ = filter(Base.Fix2(∉, Pconst), ps)
    (ss, ps′)
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


# match defslot patterns early
# retrun iterator of (ss, ps, σ) values
function _match_defslot_patterns(ss, ps, fₐ=nothing, σ=match_dict())
   ## @show :mds, ss, ps, fₐ
    if any(is_defslot, ps)
        ##_@show :XXX

    elseif any(p -> is_operation(:^)(p) && is_defslot(arguments(p)[2]), ps)
        i =  findfirst(p -> is_operation(:^)(p) && is_defslot(arguments(p)[2]), ps)
        ps′ = copy(ps)
        p = ps′[i]
        a, b = arguments(p)
        wvar = :(~x); wvar.args[2] = Symbol(join(rand("abcdefghijklmnopqrstuvwxyz", 8)))
        ps′[i] = pterm(:(^), (a, wvar))
        θ = match_commutative_sequence(ss, ps′, fₐ, (σ,))
        if !isempty(θ)
            λ = σ -> begin
                val = get(σ, wvar, nothing)
                σ = match_dict(σ, varname(b) => val)
                Base.ImmutableDict([kv for kv ∈ σ if first(kv) != wvar]...) # XXX clean me up
            end
            return (((),(),λ(σ)) for σ in θ)
        else
            ps′[i] = a
            σ = match_dict(σ, varname(b) => defslot_op_map[:(^)])
            return ((ss, ps′, σ),)
        end
    else
        return ((ss, ps, σ),)
    end
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
            p = normalize_pattern(p,s) # rewrite pattern if needed
            soperation(s) == soperation(p) || return nothing
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

# match x_ type variables
# return iterator of (ss, ps, σ)
function _match_regular_variables(ss, ps, fc=nothing, σ = match_dict())
    isempty(ps) && return ((ss, ps, σ),)
    #@show :mrv, ss, ps, σ
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
    isempty(ps) && return (σ, )
    #@show :msv, ss, ps, fc, σ

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    ss, ps = out

    _is_WILD(x) = is_slot(x) #|| is_defslot(x)
    if !isassociative(fc)
        !isempty(filter(_is_WILD, ps)) && return nothing #()
    end

    vs, vs′ = _groupby(x -> _is_WILD(x) || is_plus(x), ps)

    length(vs) > length(ss) && return nothing #(); too many plus variables

    ds = _countmap(ss)
    dplus, dstar = _countmap(vs), _countmap(vs′)

    vars = vcat(first.(dplus), first.(dstar))
    isempty(vars) && return ()

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

    iii = Iterators.map(ii) do u
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
                    vv′ = ()
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
                        return nothing # FAIL_DICT
                    end
                else
                    σ′′ = match_dict(var => vv′)
                end
                iscompatible(σ′, σ′′) || return break
                σ′ = merge_match(σ′, σ′′)
            end
        end
        iscompatible(σ, σ′) || return nothing
        return merge_match(σ, σ′)
    end

    #return iii # XXX
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
