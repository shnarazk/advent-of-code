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
    to_visit = Set(map(l -> l[1], collect(filter(l -> length(l[2]) < 4, flow))))
    part1 = length(to_visit)
    while length(to_visit) > 0
        next = Set()
        for pos in to_visit
            if pos in keys(flow)
                for neighbor in flow[pos]
                    if neighbor in keys(flow)
                        flow[neighbor] = filter(x -> x != pos, flow[neighbor])
                        if length(flow[neighbor]) < 4
                            push!(next, neighbor)
                        end
                    end
                end
                delete!(flow, pos)
                part2 += 1
            end
        end
        to_visit = next
    end
    (part1, part2)
end

@time println(run())
