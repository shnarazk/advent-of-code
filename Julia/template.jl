#!/usr/bin/env julia

using AoC



function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day01.txt", "r") do file
        # lines = String.(eachline(file)) |>
        #     s -> filter(!isempty, s) |>
        #     s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        part1 = 0
        part2 = 0
        (part1, part2)
    end
end

@time r = run()

println(r)
