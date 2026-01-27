# MatchPy

[![Build Status](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/MatchPy.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides two matching algorithms.

* An implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as `MatchPy`.

* A slight modification of a matching algorithm developed in the `SymbolicIntegration` package in [rule2.jl](https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl). This implementation only depends on the lightweight `TermInterface` package and the `Combinatorics` package.

Both find all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The latter algorithm allocates much less and is generally an order faster.
