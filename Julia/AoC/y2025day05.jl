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
    points = Dict{Tuple{Int,Bool},Int}()
    for range in ranges
        points[(range[1], false)] = get!(points, (range[1], false), 0) + 1
        points[(range[2], true)] = get!(points, (range[2], true), 0) + 1
    end
    (level, start, total) = (0, 0, 0)
    for ((n, close), count) in sort(collect(points))
        if close
            level -= count
            if level == 0
                part2 += n - start + 1
            end
        else
            if level == 0
                start = n
            end
            level += count
        end
    end
    (part1, part2)
end

@time println(run())
