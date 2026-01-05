using AoC, AoC.Parser, ParserCombinator

🔎block_line = p"[.#]+\n" > s -> collect(s)[1:3] .== '#'
🔎block = Drop(p"[0-9]+:\n") + 🔎block_line + 🔎block_line + 🔎block_line
🔎spec = ((🔎int + E"x" + 🔎int + E": ") |> l -> Int.(l)) + ((Repeat(🔎int + E" ") + 🔎int) |> l -> Int.(l))
🔎data = (Repeat(🔎block + 🔎newline) |> l -> l) + (Repeat((🔎spec |> l -> l) + 🔎newline) |> l -> l)

function run()::ANS
    part1 = 0
    parsed = parse_one(read(open(datafile(2025, 12), "r"), String), 🔎data)
    blocks = parsed[1]
    settings = parsed[2]
    for setting in settings
        w_units = setting[1][1] ÷ 3
        h_units = setting[1][2] ÷ 3
        payload = sum(setting[2])
        part1 += Int(w_units * h_units >= payload)
    end
    (part1, 0)
end

@time println(run())
