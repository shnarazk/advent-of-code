using AoC, AoC.Parser, ParserCombinator

🔎label = p"[a-z][a-z][a-z]"
🔎line = (🔎label + E": " + Repeat(🔎label + E" ") + 🔎label) |> (a) -> (String(a[1]), String.(a[2:end]))

function run()::ANS
    part1, part2 = 0, 0
    for line in eachline(open(datafile(2025, 11), "r"))
        parsed::Tuple{String, Vector{String}} = parse_one(line, 🔎line)[1]
        println(parsed)
    end
    (part1, part2)
end

@time println(run())
