using AoC

function part1(m::Matrix{Char})::Int
    count(map(
        ((i, j),) -> (s = String(m[i, j:j+3]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1) for j in 1:size(m, 2)-3])) +
    count(map(
        ((i, j),) -> (s = String(m[i:i+3, j]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 1:size(m, 2)])) +
    count(map(
        ((i, j),) -> (s = String([m[i, j], m[i+1, j+1], m[i+2, j+2], m[i+3, j+3]]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 1:size(m, 2)-3])) +
    count(map(
        ((i, j),) -> (s = String([m[i, j], m[i+1, j-1], m[i+2, j-2], m[i+3, j-3]]); s == "XMAS" || s == "SAMX"),
        [(i, j) for i in 1:size(m, 1)-3 for j in 4:size(m, 2)]))
end

function part2(m::Matrix{Char})::Int
    count(
        function ((i, j),)
            m[i, j] == 'A' &&
                ((m[i-1, j-1] == 'M' && m[i+1, j+1] == 'S') || (m[i-1, j-1] == 'S' && m[i+1, j+1] == 'M')) &&
                ((m[i-1, j+1] == 'M' && m[i+1, j-1] == 'S') || (m[i-1, j+1] == 'S' && m[i+1, j-1] == 'M'))
        end,
        [(i, j) for i in 2:size(m, 1)-1 for j in 2:size(m, 2)-1])
end

function run()::ANS
    open(datafile(2024, 4), "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        (part1(m), part2(m))
    end
end

@time println(run())
