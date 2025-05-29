#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

🔎equation = 🔎int + E": " + Repeat(🔎int + E" ", backtrack=false) + 🔎int |> s -> (s[1], Int.(s[2:end]))

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
                if x <= ans
                    push!(tmp, x)
                end
                y = val * n
                if y <= ans
                    push!(tmp, y)
                end
            end
            values = tmp
        end
    end
    if ans in values
        ans
    else
        0
    end
end

function part2(eq::Tuple)::Int
    ans = eq[1]
    values = Set()
    for n in eq[2]
        if isempty(values)
            push!(values, n)
        else
            tmp = Set()
            for val in values
                x = val + n
                if x <= ans
                    push!(tmp, x)
                end
                y = val * n
                if y <= ans
                    push!(tmp, y)
                end
                z = val * 10^(1 + Int(floor(log10(max(n, 1))))) + n
                @assert parse(Int, "$val$n") == z
                if z <= ans
                    push!(tmp, z)
                end
            end
            values = tmp
        end
    end
    if ans in values
        ans
    else
        0
    end
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day07.txt", "r") do file
        equations = String.(eachline(file)) |>
                    s -> filter(!isempty, s) |>
                         s -> map(t -> parse_one(t, 🔎equation)[1], s)
        (sum(part1.(equations)), sum(part2.(equations)))
    end
end

@time r = run()

println(r)
