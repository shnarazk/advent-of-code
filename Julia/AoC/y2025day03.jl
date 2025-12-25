using AoC, AoC.Parser, ParserCombinator

🔎line = Repeat(p"[0-9]") |> (l -> collect(map(x -> parse(Int, x), l)::Vector{Int}))

function jolt(v::Vector{Int}, len::Int)::Int
    tmp::Vector{Int} = v[end-len+1:end]
    for rn in Iterators.reverse(v[1:end-len])
        n = rn
        for (i, val) in enumerate(tmp)
            if val <= n
                tmp[i] = n
                n = val
            else
                break
            end
        end
    end
    foldl((acc, x) -> acc * 10 + x, tmp; init = 0)
end

function run()::ANS
    (part1, part2) = (0, 0)
    for line in eachline(open(datafile(2025, 3), "r"))
        setting = parse_one(line, 🔎line)[1]
        part1 += jolt(setting, 2)
        part2 += jolt(setting, 12)
    end
    (part1, part2)
end

@time println(run())
