#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

# ─── Threaded parallel_map ─────────────────
using Base.Threads            # brings @threads into scope

"""
    parallel_map(f, A::AbstractVector)

Apply `f` to every element of `A` in parallel using Julia’s threads.
Returns a new Vector of results in the same order as `A`.
"""
function parallel_map(f, A::AbstractVector)
    R = Vector{Any}(undef, length(A))
    @threads for i in eachindex(A)
        R[i] = f(A[i])
    end
    return R
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day00.txt", "r") do file
        # lines = String.(eachline(file)) |>
        #     s -> filter(!isempty, s) |>
        #     s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        part1 = 0
        part2 = 0
        (part1, part2)
    end
end

@time r = run()

println(r)
