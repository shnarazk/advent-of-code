using AoC, AoC.Parser, ParserCombinator

function check1(v::Array{Int})::Bool
    all(3 .>= diff(v) .≥ 1) || all(-3 .<= diff(v) .≤ -1)
end

function check2(v::Array{Int})::Bool
    any(i -> check1(deleteat!(copy(v), i)), 1:length(v))
end

function run()::ANS
    open(datafile(2024, 2), "r") do file
        lines =
            String.(eachline(file)) |>
            s ->
                filter(!isempty, s) |>    # ダセー!!!
                s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        part1 = map(check1, lines) |> sum
        part2 = map(check2, lines) |> sum
        (part1, part2)
    end
end

@time println(run())
