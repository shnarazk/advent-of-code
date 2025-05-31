using AoC, AoC.Parser, ParserCombinator

🔎line = 🔎int + 🔎spaces + 🔎int

function run()::ANS
    open(datafile(2024, 1), "r") do file
        data1 = []
        data2 = []
        for line in eachline(file)
            parsed = parse_one(line, 🔎line)
            push!(data1, parsed[1])
            push!(data2, parsed[2])
        end
        sort!(data1)
        sort!(data2)
        part1 = map(((a, b),) -> abs(a - b), zip(data1, data2)) |> sum
        part2 = map(x -> x * sum(data2 .== x), data1) |> sum
        (part1=part1, part2=part2)
    end
end

@time println(run())
