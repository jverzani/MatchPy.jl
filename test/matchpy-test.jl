using Test
using MatchPy

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


## -- test internal functions
@testset "exact" begin
    𝑝, 𝑠 = :(cos(sin(a))), :(cos(sin(a)))
    m = MatchPy.syntactic_match(𝑠, 𝑝)
    @test m == MatchPy.MatchDict()

    𝑝, 𝑠 = :(cos(sin(a))), :(cos(sin(b)))
    m = MatchPy.syntactic_match(𝑠, 𝑝)
    @test isnothing(m)

    𝑝, 𝑠 = :(sin(cos(a))), :(cos(a))
    m = MatchPy.syntactic_match(𝑝, 𝑠)
    @test isnothing(m)
end

@testset "associative" begin
    𝑠 = :(1 + a + b)
    𝑝 = :(1 + (~x))
    θ = MatchPy.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 1
    σ = only(θ)
    @test σ[:x] == :(a + b)

    θ = MatchPy.match_one_to_one((:(a + b + c),), :((~~~x) + (~~~y)))
    @test length(collect(θ)) == 6 # (c, a+b),(a,c+b),(b,c+a),(c+a,b),(c+b,a), (a+b,c)

    # match
    # should not match
    𝑠 = :(log(1 + (x^2/2 - x^4/24)))
    @test !isnothing(_match(:(log(1 + ~x)), 𝑠))
    @test !isnothing(_match(:(log(1 + (~~~x))), 𝑠)) # again (~x) like (~~~x)

end

@testset "constant patterns" begin
    @test isempty(MatchPy.match_sequence((:a,:b,:c), (:a,:b,:b)))    # no substitutions
    @test only(MatchPy.match_sequence((:a,:b,:c), (:a,:b,:c))) == MatchPy.MatchDict() # one trivial substitution
end

@testset "matched variables" begin

    ss, ps = (:a,:b,:c), (:(~x),:(~y),:(~z))
    σ = MatchPy.match_dict(:x => :a)

    ss′, ps′ = MatchPy._match_matched_variables(ss, ps, σ)
    @test ss′ == [:b,:c] && ps′ == [:(~y),:(~z)]

    Θ = MatchPy.match_commutative_sequence(ss, ps, nothing, (MatchPy.MatchDict(),))
    @test length(collect(Θ)) == 6

    Θ = MatchPy.match_commutative_sequence(ss, ps, nothing, (σ,))
    @test length(collect(Θ)) == 2
end


@testset "non-variable" begin
    𝑝 =:(fₘ(g(a,(~x)), g((~x),(~y)), g((~~~z))))
    𝑠 = :(fₘ(g(a,b), g(b,a), g(a,c)))
    θ = MatchPy.match_one_to_one((𝑠,), 𝑝)
    σ = only(θ)
    @test length(σ) == 3
    @test σ[:x] == :b && σ[:y] == :a && σ[:z] == [:a, :c]

end

@testset "regular variables" begin
    𝑠 = :(fₘ(a,a,a,b,b,c))
    𝑝 = :(fₘ((~x),(~x),(~~y)))
    θ = MatchPy.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 1 # σ =  ((~x) => a, (~~y) => (a, b, b, c))
    σ = only(θ)
    @test σ[:x] == :a &&  σ[:y] == [:a, :b, :b, :c]

    𝑠 = :(fₐₘ(a,a,a,b,b,c))
    𝑝 = :(fₐₘ((~x),(~x),(~~y))) # associative has (~x) like (~~~x)
    θ = MatchPy.match_one_to_one((𝑠,), 𝑝)
    @test length(collect(θ)) == 3 # ((~x) => fₐₘ(a, b), (~~y) => fₐₘ(a, c))

end

@testset "sequence variables" begin

    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~~x), :(~~~y)))
    @test length(collect(θ)) == 2 # u(a,b), u(c); u(a), u(b,c)

    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~~x), :(~~y)), :u)
    @test length(collect(θ)) == 3 # add u(a,b,c),u()

    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~x), :(~~y)), :u)
    @test length(collect(θ)) == 4


    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~~x), :(~~~y)), :(uₘ)) # are these right
    @test length(collect(θ)) == 2 #

    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~~x), :(~~y)), :(uₘ))
    @test length(collect(θ)) == 3

    θ = MatchPy.match_sequence((:a,:b,:c), (:(~~x), :(~~y)), :(uₐₘ))
    @test length(collect(θ)) == 4


end
