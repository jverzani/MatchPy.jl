## ---- simplify
##A
## Simplify = needs unwrap_const defined: e.g.:
# SymEngine
#=
simplify(x::SymEngine.Basic) = AssociativeCommutativePatternMatching.simplify(SymEngine.Basic, x)
AssociativeCommutativePatternMatching.unwrap_const(x::SymEngine.Basic) = SymEngine.unwrap_const(x)
=#

# SimpleExpressions
#=
simplify(x::SimpleExpressions.AbstractSymbolic) = AssociativeCommutativePatternMatching.simplify(SimpleExpressions.AbstractSymbolic, x)
AssociativeCommutativePatternMatching.unwrap_const(x::SimpleExpressions.AbstractSymbolic) = SimpleExpressions.unwrap_const(x)
=#


# simplify and expand
_simplify(ex, T=symtype(ex)) = __resolve(T, ex, simplify_rules)
_expand(ex, T=symtype(ex))   = __resolve(T, ex, expand_rules)

## ------- rules to apply
canonicalize = [
    :(*(~a, ~x) + *(~b, ~x) + (~!c)) => :(*(~a + ~b, ~x) + ~c),
    :(~a + (~b + ~c))          => :(+(~a,~b,~c)),
    :(~a * (~b * ~c))          => :(*(~a,~b,~c)),
    :(~a - ~a)                 => :(zero(~a)),
    :((~x)^(~z::iszero))       => :(one(~x)),
    :((~x)^(~z::isone))        => :(~x),
    :((~x::isone)^~z)          => :(one(~x)),
    :(sqrt(~x))                => :((~x)^(1//2)),
    :(cbrt(~x))                => :((~x)^(1//3)),
    #        :(ℯ^(~z)) => :(exp(~x)),
    :(exp(~z::iszero))         => 1,
    :(exp(~z::isone))          => ℯ,

    :(sin(~x)/cos(~x)) => :(tan(~x)),
    :(sin(~x)*cot(~x)) => :(cos(~x)),
    :(cos(~x)/sin(~x)) => :(cot(~x)),
    :(cos(~x)*cot(~x)) => :(sin(~x)),

]

canonicalize_expand = [
    :(*(~a + ~b,~x))           => :(*(~a, ~x) + *(~b, ~x)),
    :((~x)^(~z::iszero))       => :(one(~x)),
    :((~x)^(~z::isone))        => :(~x),
    :((~x::isone)^~z)          => :(one(~x)),

    :((~x)^(1//2))             => :(sqrt(~x)),
    :((~x)^(1//3))             => :(cbrt(~x)),

    :(ℯ^(~z)) => :(exp(~x)),
    :(exp(~z::iszero))         => 1,
    :(exp(~z::isone))          => ℯ,

    :(sin(~x)/cos(~x)) => :(tan(~x)),
    :(sin(~x)*cot(~x)) => :(cos(~x)),
    :(cos(~x)/sin(~x)) => :(cot(~x)),
    :(cos(~x)*cot(~x)) => :(sin(~x)),

]


# https://docs.sympy.org/latest/tutorials/intro-tutorial/simplification.html
powsimp = [
    :((~x)^(~!m) * (~x)^(~n) * (~!a)) => :((~a) * (~x)^(~m + ~n)),
    :((~x)^(~!m) * (~y)^(~m) * (~!a)) => :((~a) * (~x*~y)^(~m)), # needs x,y > 0
    :(((~x)^(~m))^(~n))       => :((~x)^(~m*~n)),
]
expand_pow = reverse.(powsimp)

expsimp = [
    :((~!a) * exp(~x) * exp(~y)) => :((~!a) * exp(~x + ~y)),
    :(exp(~x)^(~y))      => :(exp(~x * ~y))
]
expand_exp = reverse.(expsimp)

logsimp = [
    :((~!a)*log(~x) + (~!a)*log(~y) + (~!b))    => :((~!a) * log(~x*~y) + (~!b)),
    :((~n)* log(~x))                    => :(log((~x)^(~n))),
]
expand_log = reverse.(logsimp)

trigsimp = [
    :((~!a) * sin(~x)^2 + (~!a) * cos(~x)^2 + ~!b) => :(~a + ~!b),
    :((~!a) * sinh(~x)^2 + (~!a) * cosh(~x)^2) => :(~a*cos(2*~x)),


    :((~!a) * cos(~x)^2 - (~!a) * sin(~x)^2)   => :(~a * cos(2*~x)),
    :((~!a) * cosh(~x)^2 + (~!a) * sinh(~x)^2) => :(~a * cosh(2*~x)),


    :((~!a) * sin(~x)*cos(~y) + (~!a) * sin(~y)*cos(~x))     => :((~!a) * sin(~x + ~y)),
    :((~!a) * sinh(~x)*cosh(~y) + (~!a) * sinh(~y)*cosh(~x)) => :((~!a) * sinh(~x + ~y)),

    :((~!a) * cos(~x)*cos(~y) - (~!a) * sin(~y)*sin(~x))     => :((~!a) * cos(~x + ~y)),
    :((~!a) * cosh(~x)*cosh(~y) + (~!a) * sinh(~y)*sinh(~x)) => :((~!a) * cosh(~x + ~y)),
]
expand_trig = reverse.(trigsimp)

trigsimpa = [
    :((~!a) * (~m::iseven)*sin(~x)*cos(~x))   => :((~!a) * div(unwrap_const(~m),2)*sin(2*~x)),
    :((~!a) * (~m::iseven)*sinh(~x)*cosh(~x)) => :((~!a) * div(unwrap_const(~m),2)*sinh(2*~x)),

    :((~!a) * cos(~x)^2  + (~!a) * sin(~x)^2)   => :(~a),
    :((~!a) * cosh(~x)^2 - (~!a) * sinh(~x)^2)  => :(~a),
]

const simplify_rules = vcat(canonicalize, powsimp, expsimp, logsimp,
                      trigsimp, trigsimpa)
const expand_rules = vcat(canonicalize, expand_pow, expand_exp, expand_trig)

## -----------------------------------------------------##

# apply rules to expression
function __apply_rules(T, x, rs)
    for r ∈ rs
        pat, rhs = r
        σs = _eachmatch(pat, x)
        isempty(σs) && continue
        for σ ∈ σs
            ex =  _rewrite(T, σ, rhs)
            return ex
            #=
            if T == Expr
                !isequal(ex, rhs) && return ex
            else
                x′ = try
                    eval(ex)
                catch err
                    x
                end
                !isequal(x, x′) && return x′
            end
            =#
        end
    end
    return x
end

function __resolve(T, ex, rs)
    n = 1
    while n < 10
        !iscall(ex) && break
        ex′ = postwalk(x -> __apply_rules(T, x, rs), ex, T)
        isnothing(ex′) && return ex
        isequal(ex′, ex) && return ex
        ex = ex′
        n += 1
    end
    return ex
end
