using AoC, AoC.Parser, ParserCombinator

🔎range = (🔎int + E"-" + 🔎int) |> (n -> (n[1], n[2])::Tuple{Int, Int})
🔎line = (Repeat(🔎range + E",") + 🔎range)

"""
    return `i`-th `width`-digits number of `n`
"""
function pick(n::Int, width::Int, i::Int)::Int
    d = digits(n)
    last = length(d) - (i - 1) * width
    foldr((n, acc) -> acc * 10 + n, d[last - width + 1:last]; init = 0)
end

function repeated(n::Int, i::Int)
    foldl((acc, _) -> acc * 10 ^ length(digits(n)) + n, 1:i; init = 0)
end

function calc(start::Int, ended::Int, len::Int, result::Dict{Int, Set{Int}})::Dict{Int, Set{Int}}
    e_len = length(digits(ended))
    if e_len ÷ len < 2
        return result
    end
    if e_len % len > 0
        ended = 10 ^ ((e_len ÷ len) * len) - 1
    end
    s_len = length(digits(start))
    if s_len % len > 0
        s_len = (s_len ÷ len + 1) * len
        start = 10 ^ (s_len - 1)
    end
    if len == 1
        for d = 1:9
            for l = s_len:e_len
                x = repeated(d, l)
                if start <= x <= ended
                    if haskey(result, x)
                        push!(result[x], l)
                    else
                        result[x] = Set([l])
                    end
                end
            end
        end
    else
        for d = pick(start, len, 1):pick(ended, len, 1)
            x = repeated(d, s_len ÷ len)
            if start <= x <= ended
                if haskey(result, x)
                    push!(result[x], s_len ÷ len)
                else
                    result[x] = Set([s_len ÷ len])
                end
            end
        end
    end
    result
end

function solve(p)::Tuple{Int, Int}
    start::Int = p[1]
    ended::Int = p[2]
    dict::Dict{Int, Set{Int}} = Dict()

    for l in 1:12
        dict = calc(start, ended, l, dict)
    end
    (part1, part2) = (0, 0)
    for (n, r) in dict
        if 2 in r
            part1 += n
        end
        if collect(r) != [1]
            part2 += n
        end
    end
    (part1, part2)
end

function run()::ANS
    line::Vector{Tuple{Int, Int}} = parse_one(read(open(datafile(2025, 2), "r"), String), 🔎line)
    foldl(.+, map(solve, line); init = (0, 0))
end

@time println(run())
