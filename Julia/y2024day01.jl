#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

🔎line = 🔎int + 🔎spaces + 🔎int

function run()::NamedTuple{(:part1, :part2), Tuple{Int, Int}}
    open("../data/2024/input-day01.txt", "r") do file
        data1 = []
        data2 = []
        for line in eachline(file)
            parsed = parse_one(line, 🔎line)
            push!(data1, parsed[1])
            push!(data2, parsed[2])
        end
        sort!(data1)
        sort!(data2)
        part1 = map(((a, b),) -> abs(a - b), zip(data1, data2)) |> sum
        part2 = map(x -> x * sum(data2 .== x), data1) |> sum
        (part1 = part1, part2 = part2)
    end
end

@time r = run()

println(r)
