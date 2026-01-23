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

# XXX this should be  anoop
asexpr(x::Union{Real, Symbol, Expr}) = x
asexpr(x) = Meta.parse(string(x)) #convert(Expr, x)
meval(x) = Main.eval(x)
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



# check for types
_is_𝐹₀(::Any) = false  # 𝐹ₙ is arity of function; this is no function
_is_𝐿(x::Any) =  false #
_is_Wild(x::Any) = false # a single match (slot)
_is_DefSlot(x::Any) = false # possible default
DefSlotDefaults = Base.ImmutableDict(:(+) => 0, :(*) => 1, :(^) => 1)
_is_Slot(x::Any) = _is_Wild(x) || _is_DefSlot(x)
_is_Plus(x::Any) = false # atleast one
_is_Star(x::Any) = false    # also segment variable
_is_𝑋(x) = _is_Wild(x) || _is_Plus(x) || _is_Star(x) #

has_𝑋(x::Any) = false
has_predicate(::Any) = false

_nameof(x::Any) = nameof(x)
_nameof(x::Symbol) = x
_nameof(x::Expr) = x

# some guards
istrue(::Any) = true
isfalse(::Any) = false

# we use these conventions for variables for SymbolicUtils compatability
# Wild (slot):  ~x
# DefSlot:  ~!x
# Plus: ~~~x
# Star: ~~x

_is_𝑋(x::Expr) = iscall(x) && first(x.args) === :(~)

function has_𝑋(x::Expr)
    _is_𝑋(x) && return true
    !iscall(x) && return false
    _is_𝑋(operation(x)) && return true
    any(has_𝑋, arguments(x))
end

function _is_Wild(x::Expr)
    _is_𝑋(x) || return false
    _, x = x.args
    iscall(x) && return false
    return true
end

function _is_DefSlot(x::Expr)
    _is_𝑋(x) || return false
    _, arg = x.args
    TermInterface.is_operation(:(!))(arg) && return true
    return false
end

function has_DefSlot(pat)
    iscall(pat) || return false
    op = operation(pat)
    if op ∈ (:(+), :(*))
        any(_is_DefSlot, arguments(pat)) && return true
    elseif op == :(^)
        a, b = arguments(pat)
        _is_DefSlot(b) && return true
    end
    return false
end

# ~~~x (1 or more)
function _is_Plus(x::Expr)
    _is_𝑋(x) || return false
    _,x = x.args
    _is_𝑋(x) || return false
    _,x = x.args
    _is_𝑋(x) || return false
    return true
end

# ~~x (0, 1, or more)
function _is_Star(x::Expr)
    _is_𝑋(x) || return false # first is ~
    _,x = x.args
    _is_𝑋(x) || return false # second is ~
    _,x = x.args
    _is_𝑋(x) && return false
    return true
end

# sequence variables are star or plus
function _is_sequence(x::Expr)
    (_is_Star(x) || _is_Plus(x)) && return true
    return false
end

# return (boolean, variable, predicate)
# can have predicate for Wild, Star, Plus
# allocates
function has_predicate(x::Expr)

    _is_𝑋(x) || return (false, x, :nothing)
    _is_DefSlot(x) && return (false, x, :nothing)

    _, x_ = x.args
    isa(x_, Symbol) && return (false, x, :nothing)
    _is_𝑋(x_) || return (true, Expr(:call, :(~), x_.args[1]), x_.args[2])

    _, x_ = x_.args
    isa(x_, Symbol) && return (false, x, :nothing)
    _is_𝑋(x_) || return (true,
                         Expr(:call, :(~), Expr(:call, :(~), x_.args[1])),
                         x_.args[2])

    _, x_ = x_.args
    isa(x_, Symbol) && return (false, x, :nothing)
    _is_𝑋(x_) || return (true,
                         Expr(:call, :(~),
                              Expr(:call, :(~), Expr(:call, :(~), x_.args[1]))),
                         x_.args[2])

    return (false, x, :nothing)
end

_free_symbols(::Symbol) = Expr[]
function _free_symbols(x::Expr)
    _is_𝑋(x) && return [x]
    iscall(x) || return Expr[]
    unique(vcat(_free_symbols.(arguments(x))...))
end

# predicates
isassociative(::Any) = false
iscommutative(::Any) = false

isassociative(x::Symbol) = x ∈ (:(+), :(*))
iscommutative(x::Symbol) = x ∈ (:(+), :(*))

isassociative(::typeof(+)) = true
isassociative(::typeof(*)) = true

iscommutative(::typeof(+)) = true
iscommutative(::typeof(*)) = true

# A substitution is a collection of pairs 𝑋 -> 𝐺
MatchDict() = Base.ImmutableDict{Union{Symbol,Expr}, Any}()
function MatchDict(kv::Pair{T}, kvs::Pair{T}...) where {T <: Union{Symbol, Expr}}
    d = MatchDict()
    d = _setvalue(d, kv)
    for kv ∈ kvs
        d = _setvalue(d, kv)
    end
    d
end

function _setvalue(d, vv::Pair)
    k, v = vv
    haskey(d, k) && return d
    Base.ImmutableDict(d, vv)
end
_setvalue(d, var, value) = _setvalue(d, var => value)

const FAIL_DICT = nothing
const ϟ = FAIL_DICT # \koppa
const ∅ = ()

#  σ △ σ′ (\bigtriangleup) for every x in the intersection of the domains has same value
function iscompatible(σ, σ′)
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
function union_match!(σ, σ′)
    for kv ∈ σ′
        σ = _setvalue(σ, kv)
    end
    σ
end

function union_match(σ, σ′)
    d = MatchDict()
    for kv ∈ σ
        d = _setvalue(d, kv)
    end
    union_match!(d, σ′)
end

function union_merge(θ, σ′)
    (union_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
end


# t matches s if there is a match with σ(t) = s
soperation(f::Any) = Symbol(operation(f))

function syntactic_match(s, p, σ = MatchDict())
    if !has_𝑋(p) # no wild
        return asexpr(s) == p ? σ : ϟ
    elseif _is_Slot(p)

        haspred, var, pred = has_predicate(p)

        if haskey(σ, var)
            σ[var] != s && return ϟ
            return σ
        end

        if haspred
            if !Base.invokelatest(eval(pred), s)
                return ϟ
            end
        end
        ##_@show var, s
        σ′ = _setvalue(σ, var => s)
        return σ′

    end

    iscall(p) || return σ

    # deal with default slots
    if !iscall(s) || (iscall(s) && soperation(s) != operation(p)) &&
        any(_is_DefSlot, arguments(p)) &&
        operation(p) ∈ keys(DefSlotDefaults)
        ##_##_##_@show :defslot_test
        # try without
        # clean this up!
        σ′ = FAIL_DICT
        ##_@show :defslot_use
        if operation(p) ∈ (:*, :+)
            as, p′′ = _groupby(!_is_DefSlot, arguments(p))
            p′ = only(p′′) # must be just one slot variable
            𝑝 = length(as) == 1 ? only(as) : Expr(:call, operation(p), as...)
            σ′ = syntactic_match(s, 𝑝, σ)
        elseif operation(p) == :^
            a, p′ = arguments(p)
            _is_DefSlot(p′) || error("Def Slot is exponent in a power")
            σ′ = syntactic_match(s, a, σ)
        end
        if iscompatible(σ, σ′)
            σ′ = _setvalue(σ′, p′ => DefSlotDefaults[operation(p)])
            return union_match(σ, σ′)
        end
    end

    iscall(s)  || return σ
    f, f′ = soperation(s), soperation(p)
    f == f′ || return ϟ

    n, n′ = length(arguments(s)), length(arguments(p))
    n == n′ || return ϟ

    for (sᵢ, pᵢ) ∈ zip(arguments(s), arguments(p))
        σ′ = syntactic_match(sᵢ, pᵢ, σ)
        σ′ == ϟ && return ϟ
        !iscompatible(σ, σ′) && return ϟ
        σ = union_match(σ, σ′)
    end

    return σ
end

# θ \theta  is an iterator of substiutions;
# default is (MatchDict(),)
function match_one_to_one(ss, p, fₐ = nothing, θ = (MatchDict(),))
    ##_@show :m11, ss, p, fₐ
    n = length(ss)
    if !has_𝑋(p)     # constant symbol
        # match if p == ss(1)
        n == 1 && asexpr(only(ss)) == p && return θ
        return ∅
    elseif _is_Slot(p) && isnothing(fₐ)  # regular variable
        if n == 1
            data = only(ss)
            haspred, var, pred = has_predicate(p)
            σ′ = MatchDict()
            if haspred
                if Base.invokelatest(Main.eval(pred), data)
                    σ′ = _setvalue(σ′, var => data)
                else
                    return ∅
                end
            else
                ##_@show var,data
                σ′ = _setvalue(σ′, var => data)
            end
            return union_merge(θ, σ′)
        end

    elseif _is_𝑋(p)                      # sequence variable?
        haspred, var, pred = has_predicate(p)
        if haspred && !Base.invokelatest(Main.eval(pred), ss)
            return ∅
        end

        if _is_Slot(var) && !isnothing(fₐ) # regular and associative function
            value = mterm(Expr, fₐ, ss)
            #value = mterm(typeof(first(ss)), fₐ, ss, nothing)
            σ′ = MatchDict(var => value)
        else
            σ′ = MatchDict(var => ss)
        end
        if _is_Star(var) || n ≥ 1
            return union_merge(θ, σ′)
        end

    elseif n == 1
        s = only(ss)
        iscall(p) || return ∅

        asₚ = copy(arguments(p))

        if any(_is_DefSlot, asₚ)
            ##_@show :defslot
            # Defslots -- first check if there is a match with a slot variable
            # if so, return that. Else, replace with default value and move on.

            i = findfirst(_is_DefSlot, asₚ)
            dvar = asₚ[i]
            wvar = :(~x); wvar.args[2] = Symbol(join(rand("abcdefghijklmnopqrstuvwxyz", 8)))
            asₚ[i] = wvar
            ##_@show dvar, wvar
            𝑝 = mterm(Expr, operation(p), asₚ)
            θ′ = match_one_to_one(ss, 𝑝, fₐ, θ)
            if !isempty(θ′)
                # replace wvar with svar in each σ
                λ = σ′ -> begin
                    val = get(σ′,wvar, nothing)
                    σ′ = _setvalue(σ′, dvar => val)
                    σ = Base.ImmutableDict([kv for kv ∈ σ′ if first(kv) != wvar]...)
                    return σ
                end
                θ′′ = Iterators.map(λ, θ′)
                return θ′′
            else
                opₚ = operation(p)
                θ = (_setvalue(σ′, dvar => DefSlotDefaults[opₚ]) for σ′ ∈ θ)
                # replace pieces of `p`
                if opₚ ∈ (:(+), :(*))
                    bs = [asₚ[j] for j in 1:length(asₚ) if j != i]
                    p = mterm(Expr, opₚ, bs)
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
function match_sequence(ss, ps, fₐ=nothing, θ=(MatchDict(),))
    ##_@show :ms, ss, ps, fₐ
    n, m = length(ss), length(ps)
    nstar = count(_is_Star, ps)
    m - nstar > n && return ∅

    nplus = count(_is_Plus, ps)

    if !isnothing(fₐ)
        nplus += count(_is_Wild, ps)
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
                if (_is_Plus(pl) || _is_Star(pl)) ||
                    (_is_Wild(pl) && !isnothing(fₐ))
                    kj = isempty(ks) ? 1 : ks[j]
                    lsub = lsub + kj
                    if _is_Star(pl)
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

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (MatchDict(),))
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
        isempty(θ) && return ((ss, ps, MatchDict()), ) # <--- ?
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
    ss′′ = asexpr.(ss)
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
function _match_defslot_patterns(ss, ps, fₐ=nothing, σ=MatchDict())
    ##_@show :mds, ss, ps, fₐ

    if any(_is_DefSlot, ps)
        ##_@show :XXX

    elseif any(p -> is_operation(:^)(p) && _is_DefSlot(arguments(p)[2]), ps)
        ##_@show :YYY
        i =  findfirst(p -> is_operation(:^)(p) && _is_DefSlot(arguments(p)[2]), ps)
        ##_@show :defslot, i, ps
        ps′ = copy(ps)
        p = ps′[i]
        a, b = arguments(p)
        wvar = :(~x); wvar.args[2] = Symbol(join(rand("abcdefghijklmnopqrstuvwxyz", 8)))
        ps′[i] = mterm(Expr, :(^), (a, wvar))
        θ = match_commutative_sequence(ss, ps′, fₐ, (σ,))
        if !isempty(θ)
            λ = σ -> begin
                val = get(σ, wvar, nothing)
                σ = _setvalue(σ, b => val)
                Base.ImmutableDict([kv for kv ∈ σ if first(kv) != wvar]...)
            end
            return (((),(),λ(σ)) for σ in θ)
        else
            ##_@show i, a, ps′
            ps′[i] = a
            σ = _setvalue(σ, b => DefSlotDefaults[:(^)])
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
        ps′, ps′′ = _groupby(_is_DefSlot, ps)
        if !isempty(ps′)
            for p ∈ ps′
                σ′ = union_match(σ, MatchDict(p => DefSlotDefaults[fₐ]))
                push!(θ₁, (ss, ps′′, σ′))
            end
        end

        θ₂ = []
        for a ∈ θ₁
            push!(θ₂, a)
            ss, ps, σ = a
            ps′, ps′′ = _groupby(p -> is_operation(:^)(p) && _is_DefSlot(arguments(p)[2]), ps)
            if !isempty(ps′)
                for p ∈ ps′
                    a, b = arguments(p)
                    _is_DefSlot(a) && error("not supposed to be")
                    σ′ = union_match(σ, MatchDict(b => DefSlotDefaults[:(^)]))
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
    ps′, ps′′ = _groupby(_is_DefSlot, ps)

    # this just handles one part
    if !isempty(ps′)
        # deal with a defslot
        # defslot has default *and* no default
        σ′ = MatchDict(only(ps′) => DefSlotDefaults[fₐ])
        iscompatible(σ, σ′) || return nothing
        σ′′ = union_match(σ, σ′)
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
            p′, p′′ = _groupby(_is_DefSlot, arguments(p))
            𝑝 = Expr(:call, op, p′′...)
            σ₀ = MatchDict(only(p′) => DefSlotDefaults[op])
            iscompatible(σ, σ₀) || return nothing
            σ′ = union_match(σ, σ₀)
            θ′′ = match_one_to_one((s,), 𝑝, fₐ, (σ′,))
        elseif op == :(^)
            𝑝, p′ = arguments(p)
            _is_DefSlot(𝑝) && error("Not supposed to be")
            _is_DefSlot(p′) || error("Not supposed to be")
            σ₀ = MatchDict(p′ => DefSlotDefaults[op])
            iscompatible(σ, σ₀) || return nothing
            σ′ = union_match(σ, σ₀)
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
function _match_non_variable_patterns(ss, ps, fc=nothing, σ=MatchDict())
    ##_@show :mnvp, ss, ps, fc

    out = _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    ss, ps = out

    ps′, ps′′ = _groupby(!_is_𝑋, ps)

    pops = operation.(ps′)
    λ = x -> iscall(x) && soperation(x) ∈ pops
    ss′, ss′′  = _groupby(λ, ss)

    n = length(ps′)
    n == 0 && return ((ss, ps, (σ,)),)
    n ≤ length(ss′) || return ()

    i = Combinatorics.permutations(1:length(ss′), n)

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
function _match_regular_variables(ss, ps, fc=nothing, σ = MatchDict())
    ##_@show :mrv, ss, fc, ps
    isempty(ps) && return ((ss, ps, σ), )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing #∅

    ss, ps = out
    # fₐ is  commutative, maybe associative
    isassociative(fc) && return ((ss, ps, σ),)

    ps_reg, ps′′ = _groupby(_is_Wild, ps)
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
        σ′ = union_match(σ, σ′)
        ss′′ = _uncountmap(ds)
        (ss′′, ps′′, σ′)
    end

    return iii

end


# return iterator of matches, σ
function _match_sequence_variables(ss, ps, fc=nothing, σ = MatchDict())
    ##_@show :msv, ss, ps, fc
    isempty(ps) && return (σ, )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    _is_WILD(x) = _is_Wild(x) #|| _is_DefSlot(x)

    ss, ps = out
    if !isassociative(fc)
        !isempty(filter(_is_WILD, ps)) && return nothing #()
    end

    vs, vs′ = _groupby(x -> _is_WILD(x) || _is_Plus(x), ps)
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
        (as) -> mterm(Expr, fc, as, nothing)
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
                if _is_DefSlot(v)
                    vv′ = DefSlotDefaults[fc]
                    #return nothing # handled elsewhere?????
                elseif _is_Star(v)
                    vv′ = missing
                else
                    vv′ = nothing
                end
            else
                vv′ = isa(fc, Symbol) ? mterm(Expr, fc, vv) : vv
            end
            ##_@show v, vv′
            if !isnothing(vv′)
                haspred, var, pred = has_predicate(v)
                if haspred
                    if Base.invokelatest(eval(pred), vv′)
                        σ′′ = MatchDict(var => vv′)
                    else
                        return nothing # FAIL_DICT
                    end
                else
                    σ′′ = MatchDict(v => vv′)
                end
                iscompatible(σ′, σ′′) || break
                σ′ = union_match(σ′, σ′′)
#                for kv ∈ σ′′
#                    σ′ = _setvalue(σ′, kv)
#                end
            end
        end
        iscompatible(σ, σ′) || return nothing
        return union_match(σ, σ′)
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

_groupby(pred, t) = (t = filter(pred,t), f=filter(!pred, t))


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
            σ = union_match(σ, MatchDict(p => s)) # XXX? Check compatible?
        end
        σ == ϟ && return nothing
        (σ, ds′)
    end
    iii = Iterators.filter(!isnothing, ii)
end


### ----

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
julia> @symbolic x p; @symbolic x_
(x_,)

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
function __replace(ex, u, v)
    # Expr
    isa(u, Expr) && return _replace_arguments(ex, u, v)

    # is u function
    isa(u, Function) && return _replace_expression_head(ex, u, v)

    # is u variable, ...
    return _replace_exact(ex, u, v)
end

# copy of  CallableExpressions.expression_map_matched(pred, mapping, u)
function map_matched(ex, is_match, f)
    if !iscall(ex)
        return is_match(ex) ? f(ex) : ex
    else
        is_match(ex) && return f(ex)
        iscall(ex) || return ex
        children = map_matched.(arguments(ex), is_match, f)
        return operation(ex)(children...)
    end
end

function _replace_exact(ex, p, q)
    map_matched(ex, ==(p), _ -> q)
end

# replace expression head u with v
function _replace_expression_head(ex, u, v)
    !iscall(ex) && return ex
    args′ = (_replace_expression_head(a, u, v) for a ∈ arguments(ex))
    op = operation(ex)
    λ = op == asexpr(u) ? asexpr(v) : op
    return mterm(typeof(first(args′)), λ, args′, nothing)
    ex = λ(args′...) #maketerm(ExpressionType, λ, args′, nothing)
end

#_rewrite(u::Any, σ) = u

_rewrite(::Any, u::Union{Symbol,Number}, σ) = u
function _rewrite(::Type{T}, u::Expr, σ)  where T
    if _is_𝑋(u)
        _, var, _ = has_predicate(u)
        if haskey(σ, var)
            return σ[var]
        else
            error("No match found for $var")
        end
    end
    args = _rewrite.(T, arguments(u), (σ,))
    return mterm(typeof(first(args)), operation(u), args)
    #op = Main.eval(operation(u))
end

function _replace_arguments(ex::T, u, v) where T
    iscall(ex) || return (ex == u ? v : ex)

    σ = _match(u, ex) # sigma is nothing, (), or a substitution

    if !isnothing(σ)
        σ == () && return v # no substitution
        return _rewrite(T, v, σ)
    end

    # peel off
    op, args = operation(ex), arguments(ex)
    args′ = _replace_arguments.(args, (u,), (v,))
    #return Expr(:call, op, args...)
    return mterm(typeof(first(args)), op, args′, nothing) #op(args′...)

end


## --- interface: replacd, match, eachmatch ---
function _replace(ex, args::Pair...)
    for pr in args
        k,v = pr
        ex = __replace(ex, k, v)
    end
    ex
end

# return iterator of each possible match
function _eachmatch(pat::Expr, ex)
    if has_𝑋(pat)
        return match_one_to_one([ex], pat)
    else
        σ = syntactic_match(ex, pat)
        return isnothing(σ) ? () : (σ,)
    end
end

# return first of all possible matches, as determined by `_eachmatch`
function _match(pat::Expr, ex)
    out = _eachmatch(pat, ex)
    a = iterate(out)
    isnothing(a) && return nothing
    first(a)
end
