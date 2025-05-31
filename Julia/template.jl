using AoC

function run()::ANS
    open(datafile(2024, 0), "r") do file
        # lines = String.(eachline(file)) |>
        #     s -> filter(!isempty, s) |>
        #     s -> map(t -> Int.(parse_one(t, 🔎ints)), s)
        sum1 = 0
        sum2 = 0
        (part1=sum1, part2=sum2)
    end
end

@time println(run())
