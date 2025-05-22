#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator

open("../data/2024/input-day01.txt", "r") do file
    for line in first(eachline(file), 10)
        println(line)
        println(parse_one(line, p"\d+">d -> parse(Int, d))[1])
        # Why doesn't parse_one return Error<Int, something>?
        # I dont like it.
    end
end
