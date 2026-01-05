using AoC, AoC.Parser, ParserCombinator

🔎label = p"[a-z][a-z][a-z]"
🔎line = (🔎label + E": " + Repeat(🔎label + E" ") + 🔎label) |> (a) -> (String(a[1]), String.(a[2:end]))

function count_path(flow::Dict{String, Set{String}}, from::String, to::String, table::Dict{Tuple{String, String}, Int})::Int
    d = get(table, (from, to), nothing)
    if d !== nothing
        return d
    end
    count = 0
    for dest in get(flow, from, Set())
        count += count_path(flow, dest, to, table)
    end
    table[(from, to)] = count
    count
end

function run()::ANS
    part1, part2 = 0, 0
    flow::Dict{String, Set{String}} = Dict()
    table::Dict{Tuple{String, String}, Int} = Dict()
    for line in eachline(open(datafile(2025, 11), "r"))
        parsed::Tuple{String, Vector{String}} = parse_one(line, 🔎line)[1]
        flow[parsed[1]] = Set(parsed[2])
        for dist in parsed[2]
            table[(parsed[1], dist)] = 1
        end
    end
    part1 = count_path(flow, "you", "out", table)
    part2 = count_path(flow, "svr", "fft", table) * count_path(flow, "fft", "dac", table) * count_path(flow, "dac", "out", table)
    part2 += count_path(flow, "svr", "dac", table) * count_path(flow, "dac", "fft", table) * count_path(flow, "fft", "out", table)
    (part1, part2)
end

@time println(run())
