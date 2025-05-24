#!/usr/bin/env julia
using ParserCombinator
include("AoCParser.jl")
using .AoCParser

function part1(m::Matrix{Char})::Int
    count(map(
        ((i, j),) -> (s = String(m[i, j:j+3]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1) for j in 1:size(m, 2)-3])) +
    count(map(
        ((i, j),) -> (s = String(m[i:i+3, j]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 1:size(m, 2)])) +
    count(map(
        ((i, j),) -> (s = String([m[i, j], m[i+1, j+1], m[i+2, j+2], m[i+3, j+3]]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 1:size(m, 2)-3])) +
    count(map(
        ((i, j),) -> (s = String([m[i, j], m[i+1, j-1], m[i+2, j-2], m[i+3, j-3]]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 4:size(m, 2)]))
end

function part2(m::Matrix{Char})::Int
    size(m, 1)
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day04.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        (part1(m), part2(m))
    end
end

@time r = run()

println(r)
