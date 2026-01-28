# Lifted from SymbolicIntegration.jl test
using Test
using Random
using MatchPy

function rule2(rule::Pair{Expr, Expr}, expr)
    σ = MatchPy.match_dict()
    ms = MatchPy.check_expr_r(expr, rule.first, [σ])
    isempty(ms) && return nothing
    m = first(ms)

    rule.second==:(~~) && return m # useful for debug

    r = MatchPy.rewrite(m, rule.second)
end

@testset "General" begin
    r1 = :(sin(2*~x)) => :(2sin(~x)*cos(~x))
    @test rule2(r1, :(sin(2a))) !== nothing
end

@testset "defslot" begin
    rp = :(~!a + ~x) => :(~a)
    @test isequal(rule2(rp, :x), 0)
    @test rule2(rp, :(x+3)) ∈ (:x,3)

    rt = :(~!a * ~x) => :(~a)
    @test isequal(rule2(rt, :x), 1)
    @test rule2(rt, :(x*3)) ∈ (:x, 3)

    rpo = :((~x)^(~!a)) => :(~a)
    @test isequal(rule2(rpo, :x), 1)
    @test isequal(rule2(rpo, :(x^3)), 3)
end

@testset "neg exponent" begin
    r = :((~x::(in->!iscall(in))) ^ ~m) => :(~m)
    @test isequal(rule2(r, :(1/(x^3))), -3)
    @test isequal(rule2(r, :((1/x)^3)), -3)
    @test isequal(rule2(r, :(1/x)), -1)
    @test isequal(rule2(r, :(exp(x))), :x)
    @test isequal(rule2(r, :(sqrt(x))), 1//2)
    @test isequal(rule2(r, :(1/sqrt(x))), -1//2)
    @test isequal(rule2(r, :(1/exp(x))), Expr(:call, :-,:x))
end

@testset "special functions in rules" begin
    rs = :(sqrt(~x)) => :(~x)
    @test isequal(rule2(rs, :(sqrt(x))), :x)
    @test isequal(rule2(rs, :(x^(1//2))), :x)
    rs = :(exp(~x)) => :(~x)
    @test isequal(rule2(rs, :(exp(x+1))), :(x+1))
    @test isequal(rule2(rs, :(ℯ^x)), :x)
end

@testset "Segment" begin
    r = :(sin(+(~~a))) => :(~~a)
    # eq fails, isequal passes
    @test isequal(rule2(r, :(sin(1+x+y+z))), [1, :x, :y, :z])
end

@testset "Neim Problem" begin
    r = :((~a)^2/(~b)^~n)=>:(~n) # normal rule, neim trick not applied
    r2 = :((~a)^2*(~b)^~n)=>:(~n) # prod of powers
    r3 = :((~c)^2*(~a)^3/(~b)^~n)=>:(~n) # normal rule, neim trick not applied
    r4 = :((~c)^2*(~a)^3*(~b)^~n)=>:(~n) # prod of 3 powers
    r5 = :((~c)^~m*(~a)^3/(~b))=>:(~b)
    r6 = :((~d + ~x) * (~(!a) + ~(!b) * ~x) ^ ~(!p)) => :(~p) # prod of not all powers
    r7 = :((~c)*(~a)*(~b)^~n)=>:(~n) # prod of not all powers
    r8 = :((~!c)*(~a)^(~!m)*(~b)^~n::(x->(x==-1)))=>:(~n,~m) # prod of not all powers
    # the predicate is needed bc otherwise both (n=-1,m=-3) and (n=-3,m=-1) would be valid

    @test isequal(rule2(r, :(x^2/y^3)), 3)
    @test isequal(rule2(r2, :(x^2*y^3)), 3)
    @test isequal(rule2(r2, :(x^2/y^3)), Expr(:call, :-,3))
    @test isequal(rule2(r3, :(x^2*y^3/z^8)), 8)
    @test isequal(rule2(r4, :(x^2*y^3*z^8)), 8)
    @test isequal(rule2(r4, :(x^2*y^3/z^8)), Expr(:call, :-, 8))
    ##  @test isequal(rule2(r5, :((y)^3/(x*z^2))), :x) this still doesnt work
    sub = :((1 + x) / ((2 + 2x)^3)) # numerator is not a product
    @test isequal(rule2(r6, sub), Expr(:call,:-,3))
    sub = :((x*y) / ((2 + 2x)^3)) # numerator is a product
    @test isequal(rule2(r7, sub), Expr(:call,:-,3))

    #    @test isequal(rule2(r8, :((x) / (y*(2 + 2x)^3)))[1], -1)
    #    @test isequal(rule2(r8, :((x) / (y*(2 + 2x)^3)))[2], -3)
    pat= first(r8)
    sub = :((x) / (y*(2 + 2x)^3))
    σs = MatchPy._eachmatch(pat, sub)
    for σ ∈ σs
        @test σ[:n] == -1
    end

    pat = :((~!c)*(~a)^(~!m)*(~b)^(~!n)) # r8 w/o predicat
    σs = MatchPy._eachmatch(pat, sub)
    @test length(σs) == 2
    for σ ∈ σs
        @test σ[:n]*σ[:m] == -1
    end
end
