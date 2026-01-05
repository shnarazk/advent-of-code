using AoC, AoC.Parser, ParserCombinator

🔎target = Alt(
    Drop(E"mul(") + 🔎int + Drop(E",") + 🔎int + Drop(E")") |> x -> x[1] * x[2],
    p".*" |> x -> 0,
)

🔎do = Alt(E"do()" |> x -> true, p".*" |> x -> false)

🔎dont = Alt(E"don't()" |> x -> true, p".*" |> x -> false)

function check1(l::String)::Int
    map(i -> parse_one(l[i:end], 🔎target)[1], 1:length(l)) |> sum
end

function check2(l::String)::Int
    active = true
    sum = 0
    for i = 1:length(l)
        s::String = l[i:end]
        if s[1] != 'd' && s[1] != 'm'
            continue
        end
        if parse_one(s, 🔎do)[1]
            active = true
            continue
        end
        if parse_one(s, 🔎dont)[1]
            active = false
            continue
        end
        sum += active ? parse_one(s, 🔎target)[1] : 0
    end
    sum
end

function run()::ANS
    open(datafile(2024, 3), "r") do file
        mem = read(file, String)
        (part1 = check1(mem), part2 = check2(mem))
    end
end

@time println(run())
