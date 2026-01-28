using Test
using MatchPy
using MatchPy: _eachmatch, _replace, _match
MP, R2 = MatchPy.MP, MatchPy.R2
using TermInterface

function MatchPy.isassociative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₐ") && return true
    endswith(nm, "ₐₘ") && return true
    false
end

function MatchPy.iscommutative(x::Symbol)
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
        (pat = :(log(1 + ~x) + ~!y),
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

    for (i,(;pat, sub, len)) ∈ enumerate(ts)
        σs = _eachmatch(pat, sub, MP())
        γs = _eachmatch(pat, sub, R2())
        u = collect(σs)
        @test length(u) == len
        @test length(γs) ≤ length(u)
        #length(γs) < length(u) && (@show pat, sub, :different)
    end
end

@testset "eachmatch differences" begin

    for (pat, sub) ∈ [
        (:(~x + ~y), :(a + b + c)),    # R2 has no match (associativity)
        (:(~x + ~(~y)), :(a + b + c)), # R2 doesn't have associativity for ~x
        (:(~~x + ~~y), :(a + b + c)),  # R2 puts all matches into first segment
    ]
        σs = collect(_eachmatch(pat, sub, MP()))
        γs = _eachmatch(pat, sub, R2())

        @test length(γs) < length(σs)
    end
end

@testset "match" begin
    for M ∈ (MP(), R2())
        # match 1
        pat = :((~x)^(~x))
        sub = :((x+p)^(x+p))
        σ = _match(pat, sub,M)
        @test σ[:x] == :(x + p)

        # _match 2 wildcards
        pat = :((~x)*sin((~y)))
        sub = :(x*sin(x))
        σ = _match(pat, sub, M)
        @test σ[:y] == :x && σ[:x] == :x && length(σ) == 2

        # _match can have more than 1 substitution
        pat = :(f((~~x),(~~y)))
        sub = :(f(a,b,c))
        σ = _match(pat, sub, M)
        @test Set(vcat(collect.(values(σ))...)) == Set([:a,:b,:c])

        # empty _match returns `nothing`
        pat = :(sin(~x))
        sub = :(sin(x)^2)
        @test isnothing(_match(pat, sub, M))
    end

end



@testset "replace head" begin
    # replace operation
    ex = :(log(1 + x^2) + log(1 + x^3))
    rule = log=>log1p
    @test _replace(ex, rule) == :(log1p(1 + x ^ 2) + log1p(1 + x ^ 3))

    ex = :(f(a,a,b))
    rule = :(f(~~x)) => :(g(~~x))
    for M ∈ (MP(), R2())
        u = _replace(ex, rule, M)
        @test operation(u) == :g # :(g(Any[:a, :a, :b]))
    end
end

@testset "replace" begin

    for M ∈ (MP(), R2())

        # replace parts
        ex = :(log(1 + x^2) + log(1 + x^3))
        rule = :(log(1+(~~~x))) => :(log1p((~~~x)))
        u = _replace(ex, rule,M )
        @test u == :(log1p(x^2) + log1p(x^3))

    #@test _replace(ex, :(log(1+(~~~x))) => :(log1p((~~~x)))) == log1p(x ^ 2) + log1p(x ^ 3)

        ex = :(log(sin(x)) + tan(sin(x^2)))
        rule = sin => cos
        @test _replace(ex, rule, M) == :(log(cos(x)) + tan(cos(x ^ 2)))

        rule = :(sin(~x))=> :(tan(~x))
        @test _replace(ex, rule, M) == :(log(tan(x)) + tan(tan(x^2)))

        rule = :(sin(~x)) => :(tan((~x)/2))
        @test _replace(ex, rule, M) == :(log(tan(x/2)) + tan(tan(x^2/2)))

        rule = :(sin(~x)) => :(~x)
        @test _replace(ex, rule, M) == :(log(x) + tan(x^2))

        ex = :((1 + x^2)^2) # outer one is peeled off first by _replace
        rule = :((~x)^2) => :((~x)^4)
        @test _replace(ex, rule, M) == :((1 + (x ^ 2)) ^ 4)
        @test foldl(_replace, (rule, rule); init=ex) == :((1 + (x ^ 4)) ^ 4)


        ex = :(sin(x + x*log(x) + cos(p + x + p + x^2)))
        rule = :(cos(x + (~~x))) => :(x__)
        @test _replace(ex, rule, M) == :(sin(x + x * log(x) + x__))

        @test _replace(:x, :p=>2, M) == :x
        @test _replace(:(1 + x^2), :(x^2) => 2, M) == :(1 + 2)  # 1 + 2 evaluates to 3
        # (~x) matches different parts of expression tree in _replace
        ex = :(sin(cos(a))*cos(b))
        rule = :(cos((~x))) => :(tan((~x)))
        @test _replace(ex, rule, M) == :(sin(tan(a)) * tan(b))

        # no variable in substitution
        @test _replace(:(sin(a)), :(sin((~x))) => :x, M) == :x
        @test _replace(:(sin(a)), :(sin((~x))) => :(~x), M) == :a
        @test _replace(:(sin(a)), :(sin((~x))) => 2, M) == 2
    end
end

@testset "replace exact" begin
    for M ∈ (MP(), R2())
        # no wild card
        ex = :(x^2 + x^4)
        @test _replace(ex, :(x^2) => :x, M) == :(x + x^4)

        ex = :(x * sin(x))
        @test _replace(ex, :(x*sin(x)) => :x, M) == :x
    end
end
