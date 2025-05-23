#!/usr/bin/env julia
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

function part1(m::Matrix{Char})::Int
    size(m, 1)
end

function part2(m::Matrix{Char})::Int
    size(m, 1)
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day04.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        return (part1(m), part2(m))
    end
end

@time r = run()

println(r)
