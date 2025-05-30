#!/usr/bin/env julia
#
include("AoCUtils.jl")
include("Geometory.jl")

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
        aa = neighbors4(pos, boundary)
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

function run()::NamedTuple{(:part1,:part2),Tuple{Int,Int}}
    open(datafile(2024, 10), "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m::Matrix{Int} = hcat(map(collect, lines)...) |>
            permutedims |>
            Matrix |>
            m -> map(e -> e - '0', m)
        starts = filter(p -> m[p] == 0, collect(CartesianIndices(m)))
        # println("starts: $(length(starts))")
        sum1 = part1(m, starts)
        (sum1, 0)
    end
end

@time r = run()

println(r)
