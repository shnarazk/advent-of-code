#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

🔎rules = Repeat(🔎int + E"|" + 🔎int + 🔎newline |> s -> (s[1], s[2])) |> s -> s
🔎pages = (Repeat(🔎int + E",") + 🔎int) |> s -> Int.(s)
🔎updates = Repeat(🔎pages + 🔎newline) + 🔎pages |> s -> s
🔎data = 🔎rules + 🔎newline + 🔎updates |> s -> (s[1], s[2])

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day05-0.txt", "r") do file
        (rules, updates) = read(file, String) |> s -> parse_one(s, 🔎data)[1]
        part1 = length(rules)
        part2 = length(updates)
        (part1, part2)
    end
end

@time r = run()

println(r)
