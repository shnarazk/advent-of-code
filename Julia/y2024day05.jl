#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

🔎rules = Repeat(🔎int + E"|" + 🔎int + 🔎newline |>
        s -> (Int(s[1]), Int(s[2])), backtrack = false) |>
    s -> convert.(Tuple{Int,Int}, s)
🔎pages = Repeat(🔎int + E",", backtrack = false) + 🔎int |> s -> Int.(s)
🔎updates = Repeat(🔎pages + 🔎newline, backtrack = false) + 🔎pages |> s -> s
🔎data = 🔎rules + 🔎newline + 🔎updates |> s -> (s[1], s[2])

function total_order(m::Vector{Tuple{Int,Int}}, range::Vector{Int})::Vector{Int}
    z = filter(k -> all(k .!== [r[1] for r in m]), range)
    if isempty(z)
        range
    else
        l = total_order(
            [x for x in m if !in(x[2], z)],
            [x for x in range if !in(x, z)])
        append!(l, z)
        l
    end
end

function ordered(order::Array{Int}, pages::Array{Int})::Array{Int}
    [x for x in order if in(x, pages)]
end

function check1(rules::Vector{Tuple{Int,Int}}, pages::Vector{Int})::Int
    o = total_order([r for r in rules if in(r[1], pages) && in(r[2], pages)], pages)
    if pages == ordered(o, pages)
        pages[length(pages)÷2+1]
    else
        0
    end
end

function check2(rules::Vector{Tuple{Int,Int}}, pages::Vector{Int})::Int
    o = total_order([r for r in rules if in(r[1], pages) && in(r[2], pages)], pages)
    if (p = ordered(o, pages)) != pages
        p[length(p)÷2+1]
    else
        0
    end
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day05.txt", "r") do file
        (rules, updates) = read(file, String) |> s -> parse_one(s, 🔎data)[1]
        part1 = map(p -> check1(rules, p), updates) |> sum
        part2 = map(p -> check2(rules, p), updates) |> sum
        (part1, part2)
    end
end

@time r = run()

println(r)
