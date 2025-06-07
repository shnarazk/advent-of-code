using AoC, AoC.Geometry, AoC.Dir

function part1_aux(m::Matrix{Int}, start::Dim2)::Int
    boundary = Dim2(size(m))
    to_visit::Set{Dim2} = Set([start])
    visited::Set{Dim2} = Set()
    goals::Set{Dim2} = Set()
    while !isempty(to_visit)
        pos = pop!(to_visit)
        push!(visited, pos)
        h = m[pos]
        if h == 9
            push!(goals, pos)
            continue
        end
        for p in neighbors4(pos, boundary)
            if h + 1 == m[p] && !(p in visited)
                push!(to_visit, p)
            end
        end
    end
    length(goals)
end

function part1(m::Matrix{Int}, starts::Vector{Dim2})::Int
    map(s -> part1_aux(m, s), starts) |> sum
end

function part2_aux(m::Matrix{Int}, start::Dim2)::Int
    boundary = Dim2(size(m))
    to_visit::Vector{Dim2} = [start]
    goals::Int = 0
    while !isempty(to_visit)
        pos = pop!(to_visit)
        h = m[pos]
        if h == 9
            goals += 1
            continue
        end
        for p in neighbors4(pos, boundary)
            if h + 1 == m[p]
                push!(to_visit, p)
            end
        end
    end
    goals
end

function part2(m::Matrix{Int}, starts::Vector{Dim2})::Int
    map(s -> part2_aux(m, s), starts) |> sum
end

function run()::ANS
    open(datafile(2024, 10), "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m::Matrix{Int} = hcat(map(collect, lines)...) |>
                         permutedims |>
                         Matrix |>
                         m -> map(e -> e - '0', m)
        starts = filter(p -> m[p] == 0, collect(CartesianIndices(m)))
        sum1 = part1(m, starts)
        sum2 = part2(m, starts)
        (sum1, sum2)
    end
end

@time println(run())
