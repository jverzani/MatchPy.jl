
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


#meval(x) = Main.eval(x)
#=
function mterm(T, f::Union{Symbol, Expr}, ss, md=nothing)
    if f ∈ (:(+), :(*)) && length(ss) == 1
        return only(ss)
    else
        Expr(:call, f, ss...)
    end
end
mterm(T::Type{Symbol}, f::Symbol, ss, md=nothing) = mterm(Expr, f, ss)
mterm(T::Type{Real}, f::Symbol, ss, md=nothing) = mterm(Expr, f, ss)
function mterm(T, f::Any, ss, md=nothing)
    ##_@show T, f, ss
    maketerm(T,f,ss,md)
end
=#


# check for types
#_is_𝐹₀(::Any) = false  # 𝐹ₙ is arity of function; this is no function
#_is_𝐿(x::Any) =  false #
#_is_Wild(x::Any) = false # a single match (slot)
#=
_is_DefSlot(x::Any) = false # possible default
DefSlotDefaults = Base.ImmutableDict(:(+) => 0, :(*) => 1, :(^) => 1)
_is_Slot(x::Any) = _is_Wild(x) || _is_DefSlot(x)
_is_Plus(x::Any) = false # atleast one
_is_Star(x::Any) = false    # also segment variable
_is_𝑋(x) = _is_Wild(x) || _is_Plus(x) || _is_Star(x) #
=#
#has_predicate(::Any) = false

#=
_nameof(x::Any) = nameof(x)
_nameof(x::Symbol) = x
_nameof(x::Expr) = x
=#
# some guards
#istrue(::Any) = true
#isfalse(::Any) = false

# we use these conventions for variables for SymbolicUtils compatability
# Wild (slot):  ~x
# DefSlot:  ~!x
# Plus: ~~~x
# Star: ~~x
# ALL are regularized to :x in a match

#=
_is_𝑋(x::Expr) = iscall(x) && first(x.args) === :(~)
=#
#_is_𝑋(x::Expr) = is_𝑋(x)


#=
function _is_Wild(x::Expr)
    _is_𝑋(x) || return false
    _, x = x.args
    iscall(x) && return false
    return true
end
=#
#_is_Slot(x::Any) = _is_Wild(x) || is_defslot(x)

#=
function _is_DefSlot(x::Expr)
    _is_𝑋(x) || return false
    _, arg = x.args
    is_operation(:(!))(arg) && return true
    return false
end
=#
#_is_DefSlot(x::Expr) = is_defslot(x)
#=
function has_DefSlot(pat)
    iscall(pat) || return false
    op = operation(pat)
    if op ∈ (:(+), :(*))
        any(is_defslot, arguments(pat)) && return true
    elseif op == :(^)
        a, b = arguments(pat)
        is_defslot(b) && return true
    end
    return false
end
=#
# ~~~x (1 or more)
#=
function _is_Plus(x::Expr)
    _is_𝑋(x) || return false
    _,x = x.args
    _is_𝑋(x) || return false
    _,x = x.args
    _is_𝑋(x) || return false
    return true
end
=#
#_is_Plus(x::Expr) = is_plus(x)

# ~~x (0, 1, or more)
#=
function _is_Star(x::Expr)
    _is_𝑋(x) || return false # first is ~
    _,x = x.args
    _is_𝑋(x) || return false # second is ~
    _,x = x.args
    _is_𝑋(x) && return false
    return true
end
=#
#_is_Star(x::Expr) = is_segment(x)

# sequence variables are star or plus
#=
function _is_sequence(x::Expr)
    (is_segment(x) || is_plus(x)) && return true
    return false
end
=#

# predicates
#=
isassociative(::typeof(+)) = true
isassociative(::typeof(*)) = true

iscommutative(::typeof(+)) = true
iscommutative(::typeof(*)) = true
=#
#=
function _setvalue(d, vv::Pair)
    k, v = vv
    haskey(d, k) && return d
    Base.ImmutableDict(d, vv)
end
_setvalue(d, var, value) = _setvalue(d, var => value)
=#
#const FAIL_DICT = nothing
#const ϟ = FAIL_DICT # \koppa
const ∅ = ()

#=
function union_merge(θ, σ′)
    (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
end
=#

# t matches s if there is a match with σ(t) = s
soperation(f::Any) = Symbol(operation(f))

# θ \theta  is an iterator of substiutions;
# default is (match_dict(),)
function match_one_to_one(ss, p, fₐ = nothing, θ = (match_dict(),))
    ##_@show :m11, ss, p, fₐ
    n = length(ss)
    if !has_𝑋(p)     # constant symbol
        # match if p == ss(1)
        n == 1 && as_symbol_or_literal(only(ss)) == p && return θ
        return ∅
    elseif is_slot_or_defslot(p) && isnothing(fₐ)  # regular variable
        if n == 1
            data = only(ss)
            σ′ = match_dict()
            var = varname(p)
            if has_predicate(p)
                pred = get_predicate(p)
                if Base.invokelatest(Main.eval(pred), data)
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
            !Base.invokelatest(Main.eval(get_predicate(p)), ss)
            return ∅
        end

        if is_slot_or_defslot(p) && !isnothing(fₐ) # regular and associative function
            value = pterm(fₐ, ss)
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
            ##_@show :defslot
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
function match_sequence(ss, ps, fₐ=nothing, θ=(match_dict(),))
    ## @show :ms, ss, ps, fₐ
    n, m = length(ss), length(ps)
    nstar = count(is_segment, ps)
    m - nstar > n && return ∅
    nplus = count(is_plus, ps)

    m < n && iszero(nstar) && iszero(nplus) && return ∅

    if !isnothing(fₐ)
        nplus += count(is_slot, ps)
    end

    nfree = n - m + nstar
    nseq = nstar + nplus

    θᵣ = ∅
    itr = Base.Iterators.product((0:nfree for _ in 1:nseq)...)

    i = let θ=θ, fₐ=fₐ, ss=ss, ps=ps
        # for every distribution of free arguments among the seq. vars...
        Iterators.map(itr) do ks
            (!isempty(ks) && sum(ks) != nfree) && return nothing
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
            θ′ == () && return nothing
            return θ′
        end |> Base.Fix1(Iterators.filter, !isnothing)
    end

    i |> Iterators.flatten


end

## ----

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (match_dict(),))
    ##_@show :mcs, ss, ps, fₐ
    out = _match_constant_patterns(ss, ps)
    isnothing(out) && return ∅

    ss, ps = out

    function f0(a)
        ss, ps, σ = a
        u = _match_defslot_patterns(ss, ps, fₐ, σ)
        u
    end

    function f1(a)
        ss, ps, σ = a
        _match_non_variable_patterns(ss, ps, fₐ, σ)
    end

    function f2(a)
        # XXX why is this return an iterator for θ?
        ss, ps, θ = a
        isempty(θ) && return ((ss, ps, match_dict()), ) # <--- ?
        σ = isa(θ, AbstractDict) ? θ : first(θ)  # XXX???
        _match_regular_variables(ss, ps, fₐ, σ)
    end

    function f3(a)
        ss, ps, σ = a
        _match_sequence_variables(ss, ps, fₐ, σ)
    end

    # chain together
    itr = let ss=ss, ps=ps, θ=θ
        ((ss, ps, σ) for σ ∈ θ)
    end

    t0 =  Iterators.map(f0, itr) |>
        Iterators.flatten |>
        Base.Fix1(Iterators.filter, !isnothing)

    t1 =  Iterators.map(f1, t0) |>
        Iterators.flatten |>
        Base.Fix1(Iterators.filter, !isnothing)

    t2 = Iterators.map(f2, t1) |> Iterators.flatten |>
        Base.Fix1(Iterators.filter, !isnothing)

    t3 = Iterators.map(f3, t2) |> Iterators.flatten |>
        Base.Fix1(Iterators.filter, !isnothing)

    return t3

end

# return trimmed ss, ps or nothing
function _match_constant_patterns(ss, ps)
    ##_@show :mcp, ss, ps
    # XXX what about mismatched match?
    # XXX clean this up!

    Pconst = filter(!has_𝑋, ps)
    ss′′ = as_symbol_or_literal.(ss)
    for p ∈ Pconst
        inds = Int[]
        for (i,sᵢ) ∈ enumerate(ss′′)
            p == sᵢ && push!(inds, i)
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
    ##_@show :mmv, ss, ps
    # subtract from, ps, ss previously matched variables
    (isnothing(σ) || isempty(σ)) && return (ss, ps)

    for (p,s) ∈ σ
        for _ in 1:count(==(p), ps)
            # delete s from ss or return nothhing
            itr = applicable(iterate, s) ? s : [s] #isa(s, Tuple) ? s : (s,)
            for si ∈ itr
                i = findfirst(==(si), ss)
                isnothing(i) && return nothing
                ss = [v for (j,v) ∈ enumerate(ss) if j != i]
            end
        end
    end

    ps = [v for v in ps if v ∉ keys(σ)] #v ∉ first.(σ)) # XXX ?
    ss, ps
end


# match defslot patterns early
function _match_defslot_patterns(ss, ps, fₐ=nothing, σ=match_dict())
    ##_@show :mds, ss, ps, fₐ

    if any(is_defslot, ps)
        ##_@show :XXX

    elseif any(p -> is_operation(:^)(p) && is_defslot(arguments(p)[2]), ps)
        ##_@show :YYY
        i =  findfirst(p -> is_operation(:^)(p) && is_defslot(arguments(p)[2]), ps)
        ##_@show :defslot, i, ps
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
                Base.ImmutableDict([kv for kv ∈ σ if first(kv) != wvar]...)
            end
            return (((),(),λ(σ)) for σ in θ)
        else
            ##_@show i, a, ps′
            ps′[i] = a
            σ = match_dict(σ, varname(b) => defslot_op_map[:(^)])
            ##_@show ps′, σ
            return ((ss, ps′, σ),)
        end
    else
        return ((ss, ps, σ),)
    end

    #=
    # this checks for defslots amongst arguments
    # and in powers
    θ₁ = [(ss, ps, σ)]
    if fₐ ∈ (:(+), :(*))
        ps′, ps′′ = _groupby(is_defslot, ps)
        if !isempty(ps′)
            for p ∈ ps′
                σ′ = merge_match(σ, match_dict(p => defslot_op_map[fₐ]))
                push!(θ₁, (ss, ps′′, σ′))
            end
        end

        θ₂ = []
        for a ∈ θ₁
            push!(θ₂, a)
            ss, ps, σ = a
            ps′, ps′′ = _groupby(p -> is_operation(:^)(p) && is_defslot(arguments(p)[2]), ps)
            if !isempty(ps′)
                for p ∈ ps′
                    a, b = arguments(p)
                    is_defslot(a) && error("not supposed to be")
                    σ′ = merge_match(σ, match_dict(b => defslot_op_map[:(^)]))
                    push!(θ₂, (ss, vcat(a, ps′′), σ′))
                end
            end
        end
        θ₁ = θ₂
    end
    ##_@show σ, collect(θ₁)
    return θ₁
    =#
    #=
    # XXX
    # at top level
    ps′, ps′′ = _groupby(is_defslot, ps)

    # this just handles one part
    if !isempty(ps′)
        # deal with a defslot
        # defslot has default *and* no default
        σ′ = match_dict(only(ps′) => defslot_op_map[fₐ])
        iscompatible(σ, σ′) || return nothing
        σ′′ = merge_match(σ, σ′)
        θ = match_commutative_sequence(ss, ps′′, fₐ, (σ′′,))
    else
        θ = (σ,)
        ps′′ = ps
    end

    # XXX what do do with defslot? Need two paths:
    # one where we remove and set to default
    # one where we treat as Wild

    ps′′ = ps
    θ = (σ,)
    # at next level
    ps′, ps′′ = _groupby(has_DefSlot, ps′′)
    isempty(ps′) && return ((ss, ps′′, σ) for σ ∈ Θ)
    # look to match
    itr = Iterators.product(ps′, ss)
    i = Iterators.map(itr) do (p, s)
        # remove defslot from p,  check match
        op = operation(p)
        if op ∈ (:(+), :(*))
            p′, p′′ = _groupby(is_defslot, arguments(p))
            𝑝 = Expr(:call, op, p′′...)
            σ₀ = match_dict(only(p′) => defslot_op_map[op])
            iscompatible(σ, σ₀) || return nothing
            σ′ = merge_match(σ, σ₀)
            θ′′ = match_one_to_one((s,), 𝑝, fₐ, (σ′,))
        elseif op == :(^)
            𝑝, p′ = arguments(p)
            is_defslot(𝑝) && error("Not supposed to be")
            is_defslot(p′) || error("Not supposed to be")
            σ₀ = match_dict(p′ => defslot_op_map[op])
            iscompatible(σ, σ₀) || return nothing
            σ′ = merge_match(σ, σ₀)
            θ′′ = match_one_to_one((s,), 𝑝, fₐ, (σ′,))
        end
        isnothing(θ′′) && return nothing
        ss′, ps′ = setdiff(ss, (s,)), setdiff(ps, (p,))
        return ((ss′, ps′, σ) for σ ∈ θ′′)
    end

    return Iterators.flatten(Iterators.filter(!isnothing, i))
    =#
end

# match non_variable_patterns
# return iterator of (ss, ps, σ)
function _match_non_variable_patterns(ss, ps, fc=nothing, σ=match_dict())
   ## @show :mnvp, ss, ps, fc

    out = _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    ss, ps = out

    ps′, ps′′ = _groupby(!is_𝑋, ps)

    pops = operation.(ps′)
    λ = x -> iscall(x) && soperation(x) ∈ pops
    ss′, ss′′  = _groupby(λ, ss)

    n = length(ps′)
    n == 0 && return ((ss, ps, (σ,)),)
    n ≤ length(ss′) || return ()

    i = permutations(1:length(ss′), n)

    ii = Iterators.map(i) do inds
        𝑠𝑠′′  = vcat(ss′′, [sᵢ for (i,sᵢ) ∈ enumerate(ss′) if i ∉ inds])
        ss′′′ = ss′[inds]
        θ′ = (σ,)
        for (s,p) ∈ zip(ss′′′, ps′)
            ##_@show :mnvp, s, p

            soperation(s) == soperation(p) || return nothing
            θ′ = match_sequence(arguments(s), arguments(p), fc, θ′)
            θ′ == ∅ && return nothing
        end
        θ′ == ∅ && return nothing
        length(𝑠𝑠′′) > length(ps′′) && return nothing
        return (𝑠𝑠′′, ps′′, θ′)
    end

    return Iterators.filter(!isnothing, ii)
    iii = Iterators.flatten(Iterators.filter(!isnothing, ii))
    return iii
    return Iterators.map(identity, iii)
    return Iterators.map(θ -> (ss′′, ps′′, θ), iii)

end

# match x_ type variables
# return iterator of (ss, ps, σ)
function _match_regular_variables(ss, ps, fc=nothing, σ = match_dict())
   ## @show :mrv, ss, fc, ps
    isempty(ps) && return ((ss, ps, σ), )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing #∅

    ss, ps = out
    # fₐ is  commutative, maybe associative
   ## @show fc, isassociative(fc)
    isassociative(fc) && return ((ss, ps, σ),)

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
    _isc(ab, σ) = iscompatible(first(ab), σ)

    ii = Iterators.filter(ab -> iscompatible(first(ab), σ), i)

    iii = Iterators.map(ii) do (σ′, ds)
        σ′ = merge_match(σ, σ′)
        ss′′ = _uncountmap(ds)
        (ss′′, ps′′, σ′)
    end

    return iii

end


# return iterator of matches, σ
function _match_sequence_variables(ss, ps, fc=nothing, σ = match_dict())
    ##@show :msv, ss, ps, fc
    isempty(ps) && return (σ, )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    _is_WILD(x) = is_slot(x) #|| is_defslot(x)

    ss, ps = out
    if !isassociative(fc)
        !isempty(filter(_is_WILD, ps)) && return nothing #()
    end

    vs, vs′ = _groupby(x -> _is_WILD(x) || is_plus(x), ps)
    length(vs) > length(ss) && return nothing # ?(); too many plus variables

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
    ##_##_@show :msv,vars, svars, σ
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
                    #return nothing # handled elsewhere?????
                elseif is_segment(v)
                    vv′ = missing
                else
                    vv′ = nothing
                end
            else
                vv′ = isa(fc, Nothing) ? vv : sterm(typeof(first(vv)), fc, vv)
            end
            if !isnothing(vv′)
                var = varname(v)
                if has_predicate(v)
                    pred = get_predicate(v)
                    if Base.invokelatest(eval(pred), vv′)
                        σ′′ = match_dict(var => vv′)
                    else
                        return nothing # FAIL_DICT
                    end
                else
                    σ′′ = match_dict(var => vv′)
                end
                iscompatible(σ′, σ′′) || break
                σ′ = merge_match(σ′, σ′′)
#                for kv ∈ σ′′
#                    σ′ = match_dict(σ′, kv)
#                end
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
        σ = ()
        for (i, (p, np)) ∈ zip(inds, (dp))
            s, ns = ds′[i]
            np > ns && (σ = ϟ; break) # won't fit
            ds′[i] = s => (ns - np)
            σ = merge_match(σ, match_dict(varname(p) => s)) # XXX? Check compatible?
        end
        σ == ϟ && return nothing
        (σ, ds′)
    end
    iii = Iterators.filter(!isnothing, ii)
end
