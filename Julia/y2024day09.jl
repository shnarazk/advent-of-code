#!/usr/bin/env julia
#
include("AoCUtils.jl")

const Record = NamedTuple{(:id,:pos,:len),Tuple{Int,Int,Int}}

function decode(v::Vector{Int})::Vector{Record}
    at_disk = true
    id = 0
    pos = 0
    memmap = []
    for len in v
        if at_disk
            push!(memmap, (id, pos, len))
            id += 1
            pos += len
        else
            pos += len
        end
        at_disk = !at_disk
    end
    memmap
end

function part1(init::Vector{Record})::Int
    mem = copy(init)
    points::Int = 0
    for i in 0:(init[end].pos + init[end].len)
        if i < mem[1].pos
            points += i * mem[end].id
            if mem[end].len == 1
                pop!(mem) # remove the last element
                if isempty(mem)
                    break
                end
            else
                mem[end] = (id = mem[end].id, pos = mem[end].pos, len = mem[end].len - 1)
            end
        else
            points += i * mem[1].id
            if mem[1].pos + mem[1].len - 1 == i
                popfirst!(mem)
                if isempty(mem)
                    break
                end
            end
        end
    end
    points
end

function part2(init::Vector{Record})::Int
    0
end

function run()::NamedTuple{(:part1,:part2),Tuple{Int,Int}}
    open(datafile(2024, 9), "r") do file
        mem::Vector{Record} = read(file, String) |>
            strip |>
            collect |>
            s -> map(c -> c - '0', s) |>
            decode
        (part1(mem), part2(mem))
    end
end

@time r = run()

println(r)
