using AoC, AoC.Parser, ParserCombinator

🔎L = E"L" + 🔎int > (n -> -n)
🔎R = E"R" + 🔎int
🔎line = 🔎L | 🔎R

function run()::ANS
    (part1, part2, pos) = (0, 0, 50)
    for line in eachline(open(datafile(2025, 1), "r"))
        diff = parse_one(line, 🔎line)[1]
        part2 += Int(pos > 0 && pos + diff <= 0)
        pos += diff
        part2 += abs(pos) ÷ 100
        pos %= 100
        pos = (pos + 100) % 100
        part1 += Int(pos == 0)
    end
    (part1, part2)
end

@time println(run())
