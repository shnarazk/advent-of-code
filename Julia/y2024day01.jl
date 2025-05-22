#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator

pint = p"\d+" > s -> parse(Int, s)
pspaces = Drop(p"[ \t]*")
pline = pint + pspaces + pint

open("../data/2024/input-day01.txt", "r") do file
    data1 = []
    data2 = []
    for line in eachline(file)
        parsed = parse_one(line, pline)
        push!(data1, parsed[1])
        push!(data2, parsed[2])
    end
    sort!(data1)
    sort!(data2)
    # part1
    map(((a, b),) -> abs(a - b), zip(data1, data2)) |> sum |> println
    # part2
    map(x -> x * sum(data2 .== x), data1) |> sum |> println
end
