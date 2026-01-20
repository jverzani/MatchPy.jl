using Test
using MatchPy
using MatchPy: _eachmatch, _replace, _match
using MatchPy: syntactic_match, match_one_to_one, match_sequence, match_commutative_sequence
S = M = MatchPy

using SymEngine
@vars a b c x y z g() f() fₐ() fₘ() fₐₘ()
f ⨝ as = f(as...)

function S.isassociative(x::SymEngine.SymFunction)
    nm = string(nameof(x))
    endswith(nm, "ₐ") && return true
    endswith(nm, "ₐₘ") && return true
    false
end

function S.iscommutative(x::SymEngine.SymFunction)
    nm = string(nameof(x))
    endswith(nm, "ₘ") && return true
    false
end

## ----
# Main user interface are methods for `replace`, `match`, `eachmatch`
@testset "replace head" begin
    # replace operation
    ex = log(1 + x^2) + log(1 + x^3)
    @test _replace(ex, log=>sin) == sin(1 + (x ^ 2)) + sin(1 + (x ^ 3))

    @symbolic_variables f() g()
    @test _replace(f(a,a,b), :(f(~~~x)) => :(g(~~~x))) ==  g(a,a,b) # not g((a,a,b))
end

@testset "replace" begin
    # with wildcards
    ≈ₑ(u,v) = (x₀ = rand(); u(x₀) ≈ v(x₀))
    ≈ₚ(u,v) = (x₀ = rand(); p₀ = rand(); u(x₀, p₀) ≈ v(x₀, p₀))


    # replace parts
    ex = log(1 + x^2) + log(1 + x^3)
    @test _replace(ex, :(log(1+(~~~x))) => :(log1p((~~~x)))) == log1p(x ^ 2) + log1p(x ^ 3)

    ex = log(sin(x)) + tan(sin(x^2))
    @test _replace(ex, sin => cos) == log(cos(x)) + tan(cos(x^2))
    @test _replace(ex, :(sin(~x))=> :(tan(~x))) == log(tan(x)) + tan(tan(x^2))
    @test _replace(ex, :(sin(~x)) => :(tan((~x)/2))) == log(tan(x/2)) + tan(tan(x^2/2))
    @test _replace(ex, :(sin(~x)) => :(~x)) == log(x) + tan(x^2)

    ex = (1 + x^2)^2 # outer one is peeled off first by _replace
    pr = :((~x)^2) => :((~x)^4)
    @test _replace(ex, pr) == (1 + (x ^ 2)) ^ 4
    @test _replace(ex, pr, pr) == (1 + (x ^ 4)) ^ 4


    ex = sin(x + x*log(x) + cos(p + x + p + x^2))
    @test _replace(ex, :(cos(x + (~~~x))) => :((~~~x))) == sin(x + (x * log(x)) + p + p + (x ^ 2))

    @test _replace(x, p=>2) == x
    @test _replace(1 + x^2, x^2 => 2)() == 3  # 1 + 2 evaluates to 3


    # (~x) matches different parts of expression tree in _replace
    ex = sin(cos(a))*cos(b)
    @test _replace(ex, :(cos((~x))) => :(tan((~x)))) == sin(tan(a)) * tan(b)

    # no variable in substitution
    @test _replace(sin(a), :(sin((~x))) => x) == x
    @test _replace(sin(a), :(sin((~x))) => :(~x)) == a
    @test _replace(sin(a), :(sin((~x))) => 2) == 2
end

@testset "replace exact" begin
    # no wild card
    ex = x^2 + x^4
    @test _replace(ex, x^2 => x) == x + x^4

    ex = x * sin(x)
    @test _replace(ex, x*sin(x) => x) == x
    @test _replace(ex*cos(x), x*sin(x) => x) == ex * cos(x)

end

@testset "match" begin

    # match 1
    σ = _match(:((~x)^(~x)), (x+p)^(x+p)); @test σ[:(~x)] == x + p

    # _match 2 wildcards
    σ = _match(:((~x)*sin((~y))), x*sin(x))
    @test σ[:(~y)] == x && σ[:(~x)] == x && length(σ) == 2

    # _match can have more than 1 substitution
    # matching symbolic functions is issue with SymEngine!
    σ = _match(:(f((~~~x),(~~~y))), :(f(a,b,c)))
    @test Set(vcat(values(σ)...)) == Set([:a,:b,:c])

    # empty _match returns `nothing`
    @test isnothing(_match(:(sin(~x)), sin(x)^2))

    # eachmatch returns iterator
    sub = a + b + c
    @test isempty(_eachmatch(:(1 + (~x)), sub))
    @test length(collect(_eachmatch(:((~x) + (~y)), sub))) == 6 # associative
end

## -- test internal functions
@testset "exact" begin
    𝑝, 𝑠 = cos(sin(a)), cos(sin(a))
    m = syntactic_match(𝑠, 𝑝)
    @test m == M.MatchDict()

    𝑝, 𝑠 = cos(sin(a)), cos(sin(b))
    m = syntactic_match(𝑠, 𝑝)
    @test isnothing(m)

    m = syntactic_match(sin(cos(a)), cos(a))
    @test isnothing(m)
end

@testset "associative" begin
    𝑠 = 1 + a + b
    𝑝 = :(1 + (~x))
    Θ = match_one_to_one((𝑠,), 𝑝)
    @test length(collect(Θ)) == 1
    σ = only(Θ)
    @test σ[:(~x)] == a + b

    Θ = match_one_to_one((a + b + c,), :((~~~x) + (~~~y)))
    @test length(collect(Θ)) == 6 # (c, a+b),(a,c+b),(b,c+a),(c+a,b),(c+b,a), (a+b,c)

    # match
    # should not match
    𝑠 = log(1 + x^2/2 - x^4/24)
    @test !isnothing(_match(:(log(1 + ~x)), 𝑠))
    @test !isnothing(_match(:(log(1 + (~~~x))), 𝑠)) # again (~x) like (~~~x)

end

@testset "constant patterns" begin
    @test isempty(match_sequence((a,b,c), (a,b,b)))    # no substitutions
    @test only(match_sequence((a,b,c), (a,b,c))) == M.MatchDict() # one trivial substitution
end

@testset "matched variables" begin

    ss, ps = (a,b,c), (:(~x),:(~y),:(~z))
    σ = M.MatchDict(:(~x) => a)

    ss′, ps′ = M.match_matched_variables(ss, ps, σ)
    @test ss′ == (b,c) && ps′ == (:(~y),:(~z))

    Θ = match_commutative_sequence(ss, ps, nothing, (M.MatchDict(),))
    @test length(collect(Θ)) == 6
    Θ = match_commutative_sequence(ss, ps, nothing, (σ,))
    @test length(collect(Θ)) == 2

end


@testset "non-variable" begin
    𝑝 =:(fₘ(g(a,(~x)), g((~x),(~y)), g((~~~z))))
    𝑠 = fₘ(g(a,b), g(b,a), g(a,c))
    Θ = match_one_to_one((𝑠,), 𝑝)
    σ = only(Θ)
    @test length(σ) == 3
    @test σ[:(~x)] == b && σ[:(~y)] == a && σ[:(~~~z)] == [a, c]

end

@testset "regular variables" begin
    𝑠 = fₘ(a,a,a,b,b,c)
    𝑝 = :(fₘ((~x),(~x),(~~y)))
    Θ = match_one_to_one((𝑠,), 𝑝)
    @test length(collect(Θ)) == 1 # σ =  ((~x) => a, (~~y) => (a, b, b, c))
    σ = only(Θ)
    @test σ[:(~x)] == a &&  σ[:(~~y)] == [a, b, b, c]

    𝑠 = fₐₘ(a,a,a,b,b,c)
    𝑝 = :(fₐₘ((~x),(~x),(~~y))) # associative has (~x) like (~~~x)
    Θ = match_one_to_one((𝑠,), 𝑝)
    @test length(collect(Θ)) == 3 # ((~x) => fₐₘ(a, b), (~~y) => fₐₘ(a, c))


end

@testset "sequence variables" begin
    @vars u() uₐ() uₘ() uₐₘ()

    Θ = match_sequence((a,b,c), (:(~~~x), :(~~~y)), u)
    @test length(collect(Θ)) == 2 # u(a,b), u(c); u(a), u(b,c)

    Θ = match_sequence((a,b,c), (:(~~~x), :(~~y)), u)
    @test length(collect(Θ)) == 3 # add u(a,b,c),u()

    Θ = match_sequence((a,b,c), (:(~~x), :(~~y)), u)
    @test length(collect(Θ)) == 4


    Θ = match_sequence((a,b,c), (:(~~~x), :(~~~y)), uₘ) # are these right
    @test length(collect(Θ)) == 2 #

    Θ = match_sequence((a,b,c), (:(~~~x), :(~~y)), uₘ)
    @test length(collect(Θ)) == 3


    Θ = match_sequence((a,b,c), (:(~~x), :(~~y)), uₐₘ)
    @test length(collect(Θ)) == 4


end
