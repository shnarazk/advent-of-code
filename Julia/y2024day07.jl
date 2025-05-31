using AoC, AoC.Parser, ParserCombinator

🔎equation = 🔎int + E": " + Repeat(🔎int + E" ", backtrack=false) + 🔎int |> s -> (s[1], Int.(s[2:end]))

function part1(eq::Tuple)::Int
    ans = eq[1]
    values = Set()
    for n in eq[2]
        if isempty(values)
            push!(values, n)
        else
            tmp = Set()
            for val in values
                x = val + n
                if x <= ans
                    push!(tmp, x)
                end
                y = val * n
                if y <= ans
                    push!(tmp, y)
                end
            end
            values = tmp
        end
    end
    ans in values ? ans : 0
end

function part2(eq::Tuple)::Int
    ans = eq[1]
    values = Set()
    for n in eq[2]
        if isempty(values)
            push!(values, n)
        else
            tmp = Set()
            for val in values
                x = val + n
                if x <= ans
                    push!(tmp, x)
                end
                y = val * n
                if y <= ans
                    push!(tmp, y)
                end
                z = val * 10^(1 + Int(floor(log10(max(n, 1))))) + n
                @assert parse(Int, "$val$n") == z
                if z <= ans
                    push!(tmp, z)
                end
            end
            values = tmp
        end
    end
    ans in values ? ans : 0
end

function run()::ANS
    open(datafile(2024, 7), "r") do file
        equations = String.(eachline(file)) |>
                    s -> filter(!isempty, s) |>
                         s -> map(t -> parse_one(t, 🔎equation)[1], s)
        (sum(part1.(equations)), sum(part2.(equations)))
    end
end

@time println(run())
