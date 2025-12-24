using AoC, AoC.Parser, ParserCombinator

🔎L = E"L" + 🔎int > (n -> -n)
🔎R = E"R" + 🔎int
🔎line = 🔎L | 🔎R

function run()::ANS
    data = []
    (part1, part2) = (0, 0)
    open(datafile(2025, 1), "r") do file
        for line in eachline(file)
            parsed = parse_one(line, 🔎line)
            push!(data, parsed[1])
        end
    end
    pos = 50
    for diff in data
        part2 += Int(pos > 0 && pos + diff <= 0)
        pos += diff
        part2 += abs(pos) ÷ 100
        pos %= 100
        pos = (pos + 100) % 100
        part1 += Int(pos == 0)
    end
    (part1 = part1, part2 = part2)
end

@time println(run())
