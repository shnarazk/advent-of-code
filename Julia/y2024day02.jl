#!/usr/bin/env julia
# using Pkg
# Pkg.add("ParserCombinator")
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

function check1(v::Array{Int})::Bool
    all(3 .>= diff(v) .≥ 1) || all(-3 .<= diff(v) .≤ -1)
end

function check2(v::Array{Int})::Bool
    any(i -> check1(deleteat!(copy(v), i)), 1:length(v))
end

function run()::NamedTuple{(:part1, :part2), Tuple{Int, Int}}
    open("../data/2024/input-day02.txt", "r") do file
        # lines = [ Int.(parse_one(line, pints))
        #           for line in eachline(file)
        #           if !isempty(line) ]
        lines = String.(eachline(file)) |>
            s -> filter(!isempty, s) |>    # ダセー!!!
            s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        part1 = map(check1, lines) |> sum
        part2 = map(check2, lines) |> sum
        (part1, part2)
    end
end

@time r = run()

println(r)
