#!/usr/bin/env julia

using AoC

const D2 = CartesianIndex{2}

function within(s::D2, p::D2)::Union{D2,Nothing}
    all((1, 1) .<= Tuple(p) .<= Tuple(s)) ? p : nothing
end

function part1(s::D2, antennas::Dict{Char,Vector{D2}})::Int
    set = Set()
    for (_, l) in antennas
        for (i, p1) in enumerate(l)
            for (j, p2) in enumerate(l)
                if i < j
                    diff = p1 .- p2
                    if (p = within(s, p2 .- diff)) !== nothing
                        push!(set, p)
                    end
                    if (p = within(s, p1 .+ diff)) !== nothing
                        push!(set, p)
                    end
                end
            end
        end
    end
    length(set)
end

function part2(s::D2, antennas::Dict{Char,Vector{D2}})::Int
    set = Set()
    for (_, l) in antennas
        for (i, p1) in enumerate(l)
            for (j, p2) in enumerate(l)
                if i < j
                    diff = p1 .- p2
                    d = CartesianIndex(0, 0)
                    while (p = within(s, p2 .- d)) !== nothing
                        push!(set, p)
                        d = d .+ diff
                    end
                    d = CartesianIndex(0, 0)
                    while (p = within(s, p1 .+ d)) !== nothing
                        push!(set, p)
                        d = d .+ diff
                    end
                end
            end
        end
    end
    length(set)
end

function run()::ANS
    open(datafile(2024, 8), "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        s = CartesianIndex(size(m))
        antennas = Dict{Char,Vector{D2}}()
        for ix in CartesianIndices(m)
            c = m[ix]
            if c != '.'
                l = get(antennas, c, D2[])
                antennas[c] = push!(l, ix)
            end
        end
        (part1(s, antennas), part2(s, antennas))
    end
end

@time println(run())
