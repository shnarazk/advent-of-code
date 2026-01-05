using AoC, AoC.Parser, ParserCombinator

🔎line = p"[.S^]+" > (l) -> collect(l)
🔎grid = Repeat(🔎line + 🔎newline)

function run()::ANS
    (part1, part2) = (0, 0)
    grid = parse_one(read(open(datafile(2025, 7), "r"), String), 🔎grid)
    spiltter_lines = []
    start = 0
    for l in grid
        s::Array{Int,1} = []
        for (x, ch) in enumerate(l)
            if ch == 'S'
                start = x
            elseif ch == '^'
                push!(s, x)
            end
        end
        push!(spiltter_lines, s)
    end
    points::Dict{Int,Int} = Dict([(start, 1)])::Dict{Int,Int}
    for splitters in spiltter_lines
        next::Dict{Int,Int} = Dict()
        for (pos, n) in points
            if pos in splitters
                part1 += 1
                next[pos+1] = get(next, pos + 1, 0) + n
                next[pos-1] = get(next, pos - 1, 0) + n
            else
                next[pos] = get(next, pos, 0) + n
            end
        end
        points = next
    end
    part2 = sum(values(points))
    (part1, part2)
end

@time println(run())
