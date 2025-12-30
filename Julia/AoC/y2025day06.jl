using AoC, AoC.Parser, ParserCombinator

🔎numbers = 🔎spaces + Repeat(🔎int + 🔎spaces) + 🔎int + 🔎spaces
🔎ops     = 🔎spaces + Repeat(p"[+*]" + 🔎spaces) + p"[+*]" + 🔎spaces

function run()::ANS
    part1, part2 = 0, 0
    lines::Vector{Vector{Int}} = []
    input::Vector{String} = []
    ops = []
    for line in eachline(open(datafile(2025, 6), "r"))
        try
            nums::Vector{Int} = parse_one(line, 🔎numbers)
            push!(lines, nums)
        catch
            try
                ops = parse_one(line, 🔎ops)
            catch
                println("error")
            end
        end
        push!(input, line)
    end
    println(lines)
    println(ops)
    (part1, part2)
end

@time println(run())
