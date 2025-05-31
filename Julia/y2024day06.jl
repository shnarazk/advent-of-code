#!/usr/bin/env julia

using AoC

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
        dir = cursor.dir
        if m[pos...] == '#'
            dir = turn(dir)
            pos = cursor.pos + dir
            @assert m[pos...] != '#'
        end
        cursor = (pos=pos, dir=dir)
        passed[pos...] = true
    end
    sum(passed)
end

function is_loop(m::Matrix{Char}, cursor::NamedTuple, passed::Set)::Bool
    m = copy(m)
    m[(cursor.pos + cursor.dir)...] = '#'
    passed = copy(passed)
    while included(m, cursor.pos + cursor.dir)
        pos = cursor.pos + cursor.dir
        dir = cursor.dir
        if m[pos...] == '#'
            dir = turn(dir)
            pos = cursor.pos + dir
            if m[pos...] == '#'
                dir = turn(dir)
                pos = cursor.pos + dir
            end
        end
        cursor = (pos=pos, dir=dir)
        if cursor in passed
            return true
        else
            push!(passed, cursor)
        end
    end
    false
end

function part2(m::Matrix{Char})::Int
    loops = Set()
    cursor = (pos=collect(Tuple(findfirst(==('^'), m))), dir=[-1, 0])
    passed = Set([cursor])
    while included(m, cursor.pos + cursor.dir)
        pos = cursor.pos + cursor.dir
        dir = cursor.dir
        if m[pos...] == '#'
            dir = turn(dir)
            pos = cursor.pos + dir
            @assert m[pos...] != '#'
            cursor = (pos=cursor.pos, dir=dir)
        end
        if all(c -> c.pos != pos, passed) && is_loop(m, cursor, passed)
            push!(loops, pos)
        end
        cursor = (pos=pos, dir=dir)
        push!(passed, cursor)
    end
    length(loops)
end

function run()::ANS
    open("../data/2024/input-day06.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        (part1(m), part2(m))
    end
end

@time println(run())
