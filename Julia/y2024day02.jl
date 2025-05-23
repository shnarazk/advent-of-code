#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

function check1(v::Array{Int})
    all(3 .>= diff(v) .≥ 1) || all(-3 .<= diff(v) .≤ -1)
end

function check2(v::Array{Int})
    for i in 1:length(v)
        if check1(deleteat!(copy(v), i))
            return 1
        end
    end
    return 0
end

function run()
    open("../data/2024/input-day02.txt", "r") do file
        # lines = [ Int.(parse_one(line, pints))
        #           for line in eachline(file)
        #           if !isempty(line) ]
        lines = String.(eachline(file)) |>
            s -> filter(!isempty, s) |>    # ダセー!!!
            s -> map(t -> Int.(parse_one(t, pints)), s)
        part1 = map(check1, lines) |> sum
        part2 = map(check2, lines) |> sum
        return (part1, part2)
    end
end

@time r = run()

println(r)
