#!/usr/bin/env julia

function turn(dir::Vector{Int})::Vector{Int}
    if dir == [-1, 0]
        [0, 1]
    elseif dir == [0, 1]
        [1, 0]
    elseif dir == [1, 0]
        [0, -1]
    elseif dir == [0, -1]
        [-1, 0]
    else
        error()
    end
end

function included(m::Matrix{T}, pos::Vector{Int})::Bool where {T}
    all([1, 1] .<= pos .<= size(m))
end

function part1(m::Matrix{Char})::Int
    # println(collect(Tuple(findfirst(==('^'), m))))
    cursor = (pos=collect(Tuple(findfirst(==('^'), m))), dir=[-1, 0])
    passed = fill(false, size(m))
    passed[cursor.pos...] = true
    while included(m, cursor.pos + cursor.dir)
        pos = cursor.pos + cursor.dir
        if m[pos...] == '#'
            dir = turn(cursor.dir)
            pos = cursor.pos + dir
            @assert m[pos...] != '#'
            cursor = (pos=cursor.pos, dir=dir)
        end
        cursor = (pos=pos, dir=cursor.dir)
        passed[pos...] = true
    end
    sum(passed)
end

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day06.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        part2 = 0
        (part1(m), part2)
    end
end

@time r = run()

println(r)
