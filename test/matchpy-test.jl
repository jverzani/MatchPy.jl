using Test
using AssociativeCommutativePatternMatching
import AssociativeCommutativePatternMatching: _match, _eachmatch

function AssociativeCommutativePatternMatching.isassociative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₐ") && return true
    endswith(nm, "ₐₘ") && return true
    false
end

function AssociativeCommutativePatternMatching.iscommutative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₘ") && return true
    false
end


## -- test internal functions
@testset "syntactic_match" begin
    pat, sub = :(cos(sin(a))), :(cos(sin(a)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m == AssociativeCommutativePatternMatching.MatchDict()

    pat, sub = :(sin(~x)), :(sin(2x + cos(x)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m[:x] == :(2x + cos(x))

    pat, sub = :(F(sin(~x), ~x)), :(F(sin(2x), 2x))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m[:x] == :(2x)

    pat, sub = :(cos(sin(a))), :(cos(sin(b)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test isnothing(m)

    pat, sub = :(sin(cos(a))), :(cos(a))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test isnothing(m)

    pat = :((~F)(~x, ~y))
    sub = :(g(a,b))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test length(m) == 3
    @test m[:F] == :g


end

@testset "associative" begin
    sub = :(1 + a + b)
    pat = :(1 + (~x))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 1
    σ = only(θ)
    @test σ[:x] == :(a + b)

    θ = AssociativeCommutativePatternMatching.match_one_to_one((:(a + b + c),), :((~~~x) + (~~~y)))
    @test length(collect(θ)) == 6 # (c, a+b),(a,c+b),(b,c+a),(c+a,b),(c+b,a), (a+b,c)

    # match
    # should not match
    sub = :(log(1 + (x^2/2 - x^4/24)))
    @test !isnothing(_match(:(log(1 + ~x)), sub))
    @test !isnothing(_match(:(log(1 + (~~~x))), sub)) # again (~x) like (~~~x)

end

@testset "constant patterns" begin
    @test isempty(AssociativeCommutativePatternMatching.match_sequence((:a,:b,:c), (:a,:b,:b)))    # no substitutions
    @test only(AssociativeCommutativePatternMatching.match_sequence((:a,:b,:c), (:a,:b,:c))) == AssociativeCommutativePatternMatching.MatchDict() # one trivial substitution
end

@testset "matched variables" begin

    ss, ps = [:a,:b,:c], [:(~x),:(~y),:(~z)]
    σ₀ = AssociativeCommutativePatternMatching.match_dict()
    σ = AssociativeCommutativePatternMatching.match_dict(:x => :a)

    ss′, ps′ = AssociativeCommutativePatternMatching._match_matched_variables(ss, ps, σ)
    @test ss′ == [:b,:c] && ps′ == [:(~y),:(~z)]


    Θ = AssociativeCommutativePatternMatching.match_commutative_sequence(ss, ps, nothing, (σ₀,))
    @test length(collect(Θ)) == 6

    Θ = AssociativeCommutativePatternMatching.match_commutative_sequence(ss, ps, nothing, (σ,))
    @test length(collect(Θ)) == 2
end


@testset "non-variable" begin
    pat =:(fₘ(g(a,(~x)), g((~x),(~y)), g((~~~z))))
    sub = :(fₘ(g(a,b), g(b,a), g(a,c)))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    σ = only(θ)
    @test length(σ) == 3
    @test σ[:x] == :b && σ[:y] == :a && σ[:z] == [:a, :c]

end

@testset "regular variables" begin
    sub = :(fₘ(a,a,a,b,b,c))
    pat = :(fₘ((~x),(~x),(~~y)))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 2

    sub = :(fₐₘ(a,a,a,b,b,c))
    pat = :(fₐₘ((~x),(~x),(~~y))) # associative has (~x) like (~~~x)
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 3 # ((~x) => fₐₘ(a, b), (~~y) => fₐₘ(a, c))

end

@testset "sequence variables" begin

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~~y)])
    @test length(collect(θ)) == 2 # u(a,b), u(c); u(a), u(b,c)

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~y)], :u)
    @test length(collect(θ)) == 3 # add u(a,b,c),u()

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~x), :(~~y)], :u)
    @test length(collect(θ)) == 4


    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~~y)], :(uₘ)) # are these right
    @test length(collect(θ)) == 2 #

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~y)], :(uₘ))
    @test length(collect(θ)) == 3

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~x), :(~~y)], :(uₐₘ))
    @test length(collect(θ)) == 4


end
