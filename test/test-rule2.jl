## Fix me
using Test
using Random
using SymEngine
using MatchPy

function rule2(rule::Pair{Expr, Expr}, expr)
    σ = MatchPy.Rule2a.MatchDict()
    ms = MatchPy.Rule2a.check_expr_r(expr, rule.first, [σ])
    isempty(ms) && return nothing
    m = first(ms)

    rule.second==:(~~) && return m # useful for debug

    r = MatchPy.Rule2a.__rewrite(m, rule.second)
    return eval(r)
end

@testset "General" begin
    @vars a
    r1 = :(sin(2*~x)) => :(2sin(~x)*cos(~x))
    @test rule2(r1, sin(2a)) !== nothing
end

@testset "defslot" begin
    @vars x
    rp = :(~!a + ~x) => :(~a)
    @test isequal(rule2(rp, x), 0)
    @test isequal(rule2(rp, x+3), 3)
    rt = :(~!a * ~x) => :(~a)
    @test isequal(rule2(rt, x), 1)
    @test isequal(rule2(rt, x*3), 3)
    rpo = :((~x)^(~!a)) => :(~a)
    @test isequal(rule2(rpo, x), 1)
    @test isequal(rule2(rpo, x^3), 3)
end

@testset "neg exponent" begin
    @vars x
    r = :((~x::(in->!iscall(in))) ^ ~m) => :(~m)
    @test isequal(rule2(r, 1/(x^3)), -3)
    @test isequal(rule2(r, (1/x)^3), -3)
    @test isequal(rule2(r, 1/x), -1)
    @test isequal(rule2(r, exp(x)), x)
    @test isequal(rule2(r, sqrt(x)), 1//2)
    @test isequal(rule2(r, 1/sqrt(x)), -1//2)
    @test isequal(rule2(r, 1/exp(x)), -x)
end

@testset "special functions in rules" begin
    @vars x
    rs = :(sqrt(~x)) => :(~x)
    @test isequal(rule2(rs, sqrt(x)), x)
    @test isequal(rule2(rs, x^(1//2)), x)
    rs = :(exp(~x)) => :(~x)
    #@test isequal(rule2(rs, exp(x+1)), x+1)
    isequal(rule2(rs, exp(x+1)), x+1)
    @test isequal(rule2(rs, ℯ^x), x)
end

@testset "Segment" begin
    @vars x y z
    r = :(sin(+(~~a))) => :(~a)
    # eq fails, isequal passes
    @test isequal(rule2(r, sin(1+x+y+z)), 1+x+y+z)
end

function test_random_exprs(n_to_check::Int, depth_level::Int)
    max_args = 3
    @vars a b c d f g h i j k l m n o p q r s t u v w x y z
    sym_args = [a, b, c, d, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]
    exp_args = [:(~a), :(~b), :(~c), :(~d), :(~f), :(~g), :(~h), :(~i), :(~j), :(~k), :(~l), :(~m), :(~n), :(~o), :(~p), :(~q), :(~r), :(~s), :(~t), :(~u), :(~v), :(~w), :(~x), :(~y), :(~z)]
    associative_sym_ops = [(+, 2, max_args), (*, 2, max_args)]
    sym_ops = [associative_sym_ops..., (^, 2, 2), (sqrt, 1, 1), (exp, 1, 1), (log, 1, 1)]
    associative_exp_ops = [(:+, 2, max_args), (:*, 2, max_args)]
    exp_ops = [associative_exp_ops..., (:^, 2, 2), (:sqrt, 1, 1), (:exp, 1, 1), (:log, 1, 1)]
    # build random Expr, that dont get simplified. so no x*x and no x+(z+y) and x*(y*z)
    # depth is the max depth of the recursive expression
    # type = 1: build a Expr, type = 2: build a symbolic expression
    function build_r(depth::Int, type::Int, prev_op = nothing)
        if type==1
            if prev_op in associative_exp_ops
                op = rand(filter(x->x!=prev_op, exp_ops))
            else op = rand(exp_ops)
            end
        else
            if prev_op in associative_sym_ops
                op = rand(filter(x->x!=prev_op, sym_ops))
            else op = rand(sym_ops)
            end
        end
        args = []
        if depth==1
            # bc we dont want to have in the rule x*x or x+x
            tmp_args = []
            if type==1 tmp_args = copy(exp_args)
            else tmp_args = copy(sym_args)
            end
            for i in 1:rand(op[2]:op[3])
                choiche_idx = rand(1:length(tmp_args))
                choiche = tmp_args[choiche_idx]
                deleteat!(tmp_args, choiche_idx)
                push!(args , choiche)
            end
        else
            for i in 1:rand(op[2]:op[3])
                push!(args , build_r(rand(1:depth-1), type, op))
            end
        end
        if type==1 return Expr(:call, op[1], args...)
        else return op[1](args...)
        end
    end

    rng = RandomDevice()
    for i in 1:n_to_check
        seed = rand(rng, 1:9999999999)
        Random.seed!(seed)
        tmp = build_r(depth_level, 1)
        Random.seed!(seed)
        smbe = build_r(depth_level, 2)
        println("Testing $tmp against $smbe")

        result = rule2(tmp => Expr(:string,"yes"), smbe)
        if result !="yes"
            println("Failed testing this expression")
            return false
        end
    end
    return true

end

# this sometimes fails bc SymEngine simplications
@testset "Random expressions and rules" begin
     @test test_random_exprs(20,2)
end

@testset "Neim Problem" begin
    @vars x y z
    r = :((~a)^2/(~b)^~n)=>:(~n) # normal rule, neim trick not applied
    r2 = :((~a)^2*(~b)^~n)=>:(~n) # prod of powers
    r3 = :((~c)^2*(~a)^3/(~b)^~n)=>:(~n) # normal rule, neim trick not applied
    r4 = :((~c)^2*(~a)^3*(~b)^~n)=>:(~n) # prod of 3 powers
    r5 = :((~c)^~m*(~a)^3/(~b))=>:(~b)
    r6 = :((~d + ~x) * (~(!a) + ~(!b) * ~x) ^ ~(!p)) => :(~p) # prod of not all powers
    r7 = :((~c)*(~a)*(~b)^~n)=>:(~n) # prod of not all powers
    r8 = :((~c)*(~a)^~m*(~b)^~n::(x->(x==-1)))=>:(~n,~m) # prod of not all powers
    # the predicate is needed bc otherwise both (n=-1,m=-3) and (n=-3,m=-1) would be valid

    #@test isequal(rule2(r, x^2/y^3), 3)
    @test isequal(rule2(r2, x^2*y^3), 3)
    @test isequal(rule2(r2, x^2/y^3), -3)
    #@test isequal(rule2(r3, x^2*y^3/z^8), 8)
    @test isequal(rule2(r4, x^2*y^3*z^8), 8)
    @test isequal(rule2(r4, x^2*y^3/z^8), -8)
    # @test isequal(rule2(r5, (y)^3/(x*z^2)), x) this still doesnt work
    @test isequal(rule2(r6, (1 + x) / ((2 + 2x)^3)), -3) # numerator is not a product
    @test isequal(rule2(r7, (x*y) / ((2 + 2x)^3)), -3) # numerator is a product
    @test isequal(rule2(r8, (x) / (y*(2 + 2x)^3))[1], -1)
    @test isequal(rule2(r8, (x) / (y*(2 + 2x)^3))[2], -3)
    # denominator is a product
end
