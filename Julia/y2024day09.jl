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
        end
        at_disk = !at_disk
    end
    memmap
end

function part1(init::Vector{Record})::Int
    0
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
        println(mem)
        (part1(mem), part2(mem))
    end
end

@time r = run()

println(r)
