using AoC, AoC.Parser, ParserCombinator, AoC.Dir

🔎line = p"[.@]+" > (l) -> map((c -> c == '@'), collect(l))
🔎grid = Repeat(🔎line + 🔎newline)

function run()::ANS
    (part1, part2) = (0, 0)
    grid = parse_one(read(open(datafile(2025, 4), "r"), String), 🔎grid)
    flow = Dict()
    for (y, l) in enumerate(grid)
        for (x, b) in enumerate(l)
            if b
                flow[CartesianIndex(x, y)] = []
            end
        end
    end
    for (pos, depends) in flow
        for diff in [
            Dir.U,
            Dir.R,
            Dir.D,
            Dir.L,
            Dir.U + Dir.R,
            Dir.R + Dir.D,
            Dir.D + Dir.L,
            Dir.L + Dir.U,
        ]
            neighbor = pos + diff
            if neighbor in keys(flow)
                push!(depends, neighbor)
            end
        end
    end
    part1 = length(filter(l -> length(l[2]) < 4, collect(flow)))
    (part1, part2)
end

@time println(run())
