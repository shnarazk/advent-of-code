using AoC, AoC.Parser, ParserCombinator

struct Stone
    mark::Int
    level::Int
end

function even_digits(n::Int)::Union{Int,Nothing}
    d = 0
    while 0 < n
        d += 1
        n = div(n, 10)
    end
    d % 2 == 0 ? d / 2 : nothing
end

# @assert even_digits(10) == 1
# @assert even_digits(21) == 1
# @assert even_digits(2134) == 2
# @assert even_digits(2) == nothing
# @assert even_digits(213) == nothing

function divide(stone::Stone)::Union{Tuple{Stone,Stone},Nothing}
    if (n = even_digits(stone.mark)) !== nothing
        a = stone.mark
        b = 0
        base = 1
        m = n
        for _ in 1:n
            b += (a % 10) * base
            a = div(a, 10)
            base *= 10
        end
        (Stone(a, stone.level + 1), Stone(b, stone.level + 1))
    else
        nothing
    end
end

# @assert divide(Stone(82, 0)) == (Stone(8, 1), Stone(2, 1))
# @assert divide(Stone(8201, 1)) == (Stone(82, 2), Stone(1, 2))
# @assert divide(Stone(832, 0)) == nothing

function count(stone::Stone, depth::Int)::Int
    if stone.level == depth
        1
    elseif stone.mark == 0
        count(Stone(1, stone.level + 1), depth)
    elseif (p = divide(stone)) !== nothing
        count(p[1], depth) + count(p[2], depth)
    else
        count(Stone(stone.mark * 2024, stone.level + 1), depth)
    end
end

function part1(data::Vector{Stone})::Int
    map(s -> count(s, 25), data) |> sum
end

function run()::ANS
    open(datafile(2024, 11), "r") do file
        data = read(file, String) |> strip |> s -> Int.(parse_one(s, 🔎ints)) |>
            s -> map(n -> Stone(n, 0), s)
        println(data)
        sum1 = part1(data)
        sum2 = 0
        (part1=sum1, part2=sum2)
    end
end

@time println(run())
