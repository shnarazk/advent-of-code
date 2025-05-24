#!/usr/bin/env julia
#
include("Dir.jl")
using .Dirs

println(pos(Up) + pos(Right))

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day06-0.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        println(m)
        part1 = 0
        part2 = 0
        (part1, part2)
    end
end

@time r = run()

println(r)
