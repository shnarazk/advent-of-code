using AoC, AoC.Parser, ParserCombinator

🔎line = 🔎int + E"," + 🔎int > (a, b) -> (a, b)

# 変換関数対を返すべきだが
function makeCompactSpace(base::Set{CartesianIndex})::Tuple{Dict{Int, Int}, Dict{Int, Int}}
    xs::Set{Tuple{Int, Int}} = Set()
    ys::Set{Tuple{Int, Int}} = Set()
    for pos in base
        push!(xs, (pos[1], pos[1]))
        push!(ys, (pos[2], pos[2]))
    end
    vec_x::Vector{Tuple{Int, Int}} = collect(xs)
    vec_y::Vector{Tuple{Int, Int}} = collect(ys)
    sort!(vec_x)
    sort!(vec_y)
    (Dict(vec_x), Dict(vec_y))
end

function run()::ANS
    part1, part2 = 0, 0
    points::Set{CartesianIndex} = Set()
    for line in eachline(open(datafile(2025, 9), "r"))
        parsed::Tuple{Int, Int} = parse_one(line, 🔎line)[1]
        push!(points, CartesianIndex(parsed[1], parsed[2]))
    end
    println(points)
    compactSpace = makeCompactSpace(points)
    println(compactSpace)
    (part1, part2)
end

@time println(run())
