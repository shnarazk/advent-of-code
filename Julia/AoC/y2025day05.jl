using AoC, AoC.Parser, ParserCombinator

🔎ranges = Repeat((🔎int + E"-" + 🔎int + 🔎newline) > (a, b) -> (a::Int, b::Int))
🔎line = (🔎ranges |> (a) -> a) + 🔎newline + (Repeat(🔎int + 🔎newline) |> (a) -> a)

function run()::ANS
    (part1, part2) = (0, 0)
    parsed = parse_one(read(open(datafile(2025, 5), "r"), String), 🔎line)
    ranges = parsed[1]
    ids = parsed[2]
    for id in ids
        if any(range -> range[1] <= id <= range[2], ranges)
            part1 += 1
        end
    end
    # part2
    (part1, part2)
end

@time println(run())
