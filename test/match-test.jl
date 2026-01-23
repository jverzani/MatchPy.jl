using Test
using MatchPy
using MatchPy: _eachmatch, _replace, _match
using MatchPy: syntactic_match, match_one_to_one, match_sequence, match_commutative_sequence
S = M = MatchPy
using TermInterface

function M.isassociative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₐ") && return true
    endswith(nm, "ₐₘ") && return true
    false
end

function M.iscommutative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₘ") && return true
    false
end




## ----
# Main user interface are methods for `replace`, `match`, `eachmatch`

@testset "_eachmatch" begin
    ts = [
        # single variables
        (pat = :(~x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~!x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~~x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~~~x),
         sub = :(a + b + c),
         len = 1),

        # multiple variables
        (pat = :(~x + ~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~x + ~!y),
         sub = :(a),
         len = 1),
        (pat = :(~x + ~!y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~x + ~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~x + ~~~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~!x + ~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~!x + ~~~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~~x + ~~y),
         sub = :(a + b + c),
         len = 8),
        (pat = :(~~x + ~~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~~~x + ~~~y),
         sub = :(a + b + c),
         len = 6),

        # def slot with ^
        (pat = :((~x)^(~!y)),
         sub = :(a),
         len = 1),
        (pat = :((~x)^(~!y)),
         sub = :(a^2),
         len = 1),
         (pat = :(~x + (~y)^(~!z)),
         sub = :(a + b),
         len = 2),
        (pat = :(~!x + (~y)^(~!z)),
         sub = :(a + b),
         len = 2),

        # wrapped in functions
        (pat = :(log(~x) + log(~y)),
         sub = :(log(a) + log(b)),
         len = 2),
        (pat = :(log(~x) + ~!y),
         sub = :(log(a) + log(b)),
         len = 2),
        (pat = :(log(~x) + log(~y) + log(~z)),
         sub = :(log(a) + log(b) + log(c)),
         len = 6),



        (pat = :(log(1 + ~x)),
         sub = :(log(1 + x^2)),
         len = 1),
        (pat = :(log(1 + ~x)),
         sub = :(log(1 + x) + log(1 + x^2)),
         len = 0),
        (pat = :(log(1 + ~x) + ~!x),
         sub = :(log(1 + x) + log(1 + x^2)),
         len = 2),


        (pat = :(log(log(~~~x + ~~~y))),
         sub = :(log(log(a + b + c))),
         len = 6),
        (pat = :(log(log(~~~x + ~!y))),
         sub = :(log(log(a + b + c))),
         len = 6),
        (pat = :(~!x + log(log(~y))),
         sub = :(log(log(a)) + log(log(b))),
         len = 2),

        (pat = :(f(~~~x, ~~~y)),
         sub = :(f(a,b,c)),
         len = 2),
        (pat = :(f(~~x, ~~y)),
         sub = :(f(a,b,c)),
         len = 4),
        (pat = :(fₐ(~~~x, ~~~y)),
         sub = :(fₐ(a,b,c)),
         len = 2),
        (pat = :(fₐ(~~x, ~~y)),
         sub = :(fₐ(a,b,c)),
         len = 4),
        (pat = :(fₐₘ(~~~x, ~~~y)),
         sub = :(fₐₘ(a,b,c)),
         len = 6),
        (pat = :(fₐₘ(~~x, ~~y)),
         sub = :(fₐₘ(a,b,c)),
         len = 8),

    ]

    for (;pat, sub, len) ∈ ts
        u = collect(_eachmatch(pat, sub))
        @test length(u) == len
    end

end

@testset "match" begin

    # match 1
    pat = :((~x)^(~x))
    sub = :((x+p)^(x+p))
    σ = _match(pat, sub)
    @test σ[:(~x)] == :(x + p)

    # _match 2 wildcards
    pat = :((~x)*sin((~y)))
    sub = :(x*sin(x))
    σ = _match(pat, sub)
    @test σ[:(~y)] == :x && σ[:(~x)] == :x && length(σ) == 2

    # _match can have more than 1 substitution
    pat = :(f((~~~x),(~~~y)))
    sub = :(f(a,b,c))
    σ = _match(pat, sub)
    @test Set(vcat(values(σ)...)) == Set([:a,:b,:c])

    # empty _match returns `nothing`
    pat = :(sin(~x))
    sub = :(sin(x)^2)
    @test isnothing(_match(pat, sub))

end



@testset "replace head" begin
    # replace operation
    ex = :(log(1 + x^2) + log(1 + x^3))
    rule = log=>sin
    @test _replace(ex, rule) == :(sin(1 + x ^ 2) + sin(1 + x ^ 3))

    ex = :(f(a,a,b))
    rule = :(f(~~~x)) => :(g(~~~x))
    u = _replace(ex, rule)
    @test operation(u) == :g # :(g(Any[:a, :a, :b]))

end

@testset "replace" begin

    # replace parts
    ex = :(log(1 + x^2) + log(1 + x^3))
    rule = :(log(1+(~~~x))) => :(log1p((~~~x)))
    u = _replace(ex, rule)
    @test u == :(log1p(x^2) + log1p(x^3))


    #@test _replace(ex, :(log(1+(~~~x))) => :(log1p((~~~x)))) == log1p(x ^ 2) + log1p(x ^ 3)

    ex = :(log(sin(x)) + tan(sin(x^2)))
    rule = sin => cos
    @test _replace(ex, rule) == :(log(cos(x)) + tan(cos(x ^ 2)))

    rule = :(sin(~x))=> :(tan(~x))
    @test _replace(ex, rule) == :(log(tan(x)) + tan(tan(x^2)))

    rule = :(sin(~x)) => :(tan((~x)/2))
    @test _replace(ex, rule) == :(log(tan(x/2)) + tan(tan(x^2/2)))

    rule = :(sin(~x)) => :(~x)
    @test _replace(ex, rule) == :(log(x) + tan(x^2))

    ex = :((1 + x^2)^2) # outer one is peeled off first by _replace
    rule = :((~x)^2) => :((~x)^4)
    @test _replace(ex, rule) == :((1 + (x ^ 2)) ^ 4)
    @test _replace(ex, rule, rule) == :((1 + (x ^ 4)) ^ 4)


    ex = :(sin(x + x*log(x) + cos(p + x + p + x^2)))
    rule = :(cos(x + (~~~x))) => :((~~~x))
    @test _replace(ex, rule) == :(sin(x + x * log(x) + (p + p + x ^ 2)))

    @test _replace(:x, :p=>2) == :x
    @test _replace(:(1 + x^2), :(x^2) => 2) == :(1 + 2)  # 1 + 2 evaluates to 3


    # (~x) matches different parts of expression tree in _replace
    ex = :(sin(cos(a))*cos(b))
    rule = :(cos((~x))) => :(tan((~x)))
    @test _replace(ex, rule) == :(sin(tan(a)) * tan(b))

    # no variable in substitution
    @test _replace(:(sin(a)), :(sin((~x))) => :x) == :x
    @test _replace(:(sin(a)), :(sin((~x))) => :(~x)) == :a
    @test _replace(:(sin(a)), :(sin((~x))) => 2) == 2
end

@testset "replace exact" begin
    # no wild card
    ex = :(x^2 + x^4)
    @test _replace(ex, :(x^2) => :x) == :(x + x^4)

    ex = :(x * sin(x))
    @test _replace(ex, :(x*sin(x)) => :x) == :x
end




## -- test internal functions
@testset "exact" begin
    𝑝, 𝑠 = :(cos(sin(a))), :(cos(sin(a)))
    m = M.syntactic_match(𝑠, 𝑝)
    @test m == M.MatchDict()

    𝑝, 𝑠 = :(cos(sin(a))), :(cos(sin(b)))
    m = M.syntactic_match(𝑠, 𝑝)
    @test isnothing(m)

    𝑝, 𝑠 = :(sin(cos(a))), :(cos(a))
    m = M.syntactic_match(𝑝, 𝑠)
    @test isnothing(m)
end

@testset "associative" begin
    𝑠 = :(1 + a + b)
    𝑝 = :(1 + (~x))
    θ = M.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 1
    σ = only(θ)
    @test σ[:(~x)] == :(a + b)

    θ = M.match_one_to_one((:(a + b + c),), :((~~~x) + (~~~y)))
    @test length(collect(θ)) == 6 # (c, a+b),(a,c+b),(b,c+a),(c+a,b),(c+b,a), (a+b,c)

    # match
    # should not match
    𝑠 = :(log(1 + (x^2/2 - x^4/24)))
    @test !isnothing(_match(:(log(1 + ~x)), 𝑠))
    @test !isnothing(_match(:(log(1 + (~~~x))), 𝑠)) # again (~x) like (~~~x)

end

@testset "constant patterns" begin
    @test isempty(M.match_sequence((:a,:b,:c), (:a,:b,:b)))    # no substitutions
    @test only(M.match_sequence((:a,:b,:c), (:a,:b,:c))) == M.MatchDict() # one trivial substitution
end

@testset "matched variables" begin

    ss, ps = (:a,:b,:c), (:(~x),:(~y),:(~z))
    σ = M.MatchDict(:(~x) => :a)

    ss′, ps′ = M._match_matched_variables(ss, ps, σ)
    @test ss′ == [:b,:c] && ps′ == [:(~y),:(~z)]

    Θ = M.match_commutative_sequence(ss, ps, nothing, (M.MatchDict(),))
    @test length(collect(Θ)) == 6

    Θ = M.match_commutative_sequence(ss, ps, nothing, (σ,))
    @test length(collect(Θ)) == 2
end


@testset "non-variable" begin
    𝑝 =:(fₘ(g(a,(~x)), g((~x),(~y)), g((~~~z))))
    𝑠 = :(fₘ(g(a,b), g(b,a), g(a,c)))
    θ = M.match_one_to_one((𝑠,), 𝑝)
    σ = only(θ)
    @test length(σ) == 3
    @test σ[:(~x)] == :b && σ[:(~y)] == :a && σ[:(~~~z)] == [:a, :c]

end

@testset "regular variables" begin
    𝑠 = :(fₘ(a,a,a,b,b,c))
    𝑝 = :(fₘ((~x),(~x),(~~y)))
    θ = M.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 1 # σ =  ((~x) => a, (~~y) => (a, b, b, c))
    σ = only(θ)
    @test σ[:(~x)] == :a &&  σ[:(~~y)] == [:a, :b, :b, :c]

    𝑠 = :(fₐₘ(a,a,a,b,b,c))
    𝑝 = :(fₐₘ((~x),(~x),(~~y))) # associative has (~x) like (~~~x)
    θ = M.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 3 # ((~x) => fₐₘ(a, b), (~~y) => fₐₘ(a, c))

end

@testset "sequence variables" begin

    θ = M.match_sequence((:a,:b,:c), (:(~~~x), :(~~~y)))
    @test length(collect(θ)) == 2 # u(a,b), u(c); u(a), u(b,c)

    θ = M.match_sequence((:a,:b,:c), (:(~~~x), :(~~y)), :u)
    @test length(collect(θ)) == 3 # add u(a,b,c),u()

    θ = M.match_sequence((:a,:b,:c), (:(~~x), :(~~y)), :u)
    @test length(collect(θ)) == 4


    θ = M.match_sequence((:a,:b,:c), (:(~~~x), :(~~~y)), :(uₘ)) # are these right
    @test length(collect(θ)) == 2 #

    θ = M.match_sequence((:a,:b,:c), (:(~~~x), :(~~y)), :(uₘ))
    @test length(collect(θ)) == 3

    θ = M.match_sequence((:a,:b,:c), (:(~~x), :(~~y)), :(uₐₘ))
    @test length(collect(θ)) == 4


end
