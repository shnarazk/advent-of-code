using AoC, AoC.Parser, ParserCombinator

🔎line = 🔎int + E"," + 🔎int > (a, b) -> (a, b)

function run()::ANS
    part1, part2 = 0, 0
    for line in eachline(open(datafile(2025, 9), "r"))
        parsed::Tuple{Int, Int} = parse_one(line, 🔎line)[1]
        println(parsed)
    end
    (part1, part2)
end

@time println(run())
