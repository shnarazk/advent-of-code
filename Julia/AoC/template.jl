using AoC, AoC.Parser, ParserCombinator

function run()::ANS
    open(datafile(2025, 0), "r") do file
        # lines = String.(eachline(file)) |>
        #     s -> filter(!isempty, s) |>
        #     s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        part1 = 0
        part2 = 0
        (part1, part2)
    end
end

@time println(run())
