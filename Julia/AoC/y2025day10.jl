using AoC, AoC.Parser, ParserCombinator

🔎indicator = E"[" + p"[.#]+" + E"] "
🔎button = E"(" + Repeat(🔎int + E",") + 🔎int + E")" |> b -> Int.(b) #  [b]
🔎buttons = Repeat(🔎button + E" ") |> bs -> bs
🔎requirment = E"{" + Repeat(🔎int + E",") + 🔎int + E"}" |> r -> Int.(r)

  
🔎line = 🔎indicator + 🔎buttons + 🔎requirment

function run()::ANS
    part1, part2 = 0, 0
    for line in eachline(open(datafile(2025, 10), "r"))
        parsed = parse_one(line, 🔎line)
        buttons::Vector{Vector{Int}} = parsed[2]
        requirment::Vector{Int} = parsed[3]
        # println(buttons)
    end
    (part1, part2)
end

@time println(run())
