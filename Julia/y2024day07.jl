#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

🔎equation = 🔎int + E": " + Repeat(🔎int + E" ") + 🔎int |> s -> (s[1], Int.(s[2:end]))

function part1(eq::Tuple)::Int
    ans = eq[1]
    values = Set()
    for n in eq[2]
        if isempty(values)
            push!(values, n)
        else
            tmp = Set()
            for val in values
                x = val + n
                if x == ans
                    return ans
                else
                    push!(tmp, x)
                end
                y = val * n
                if y == ans
                    return ans
                else
                    push!(tmp, y)
                end
            end
            values = tmp
        end
    end
    0
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day07.txt", "r") do file
        equations = String.(eachline(file)) |>
                    s -> filter(!isempty, s) |>
                         s -> map(t -> parse_one(t, 🔎equation)[1], s)
        part2 = 0
        (sum(part1.(equations)), part2)
    end
end

@time r = run()

println(r)
