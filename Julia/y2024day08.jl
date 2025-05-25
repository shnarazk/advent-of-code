#!/usr/bin/env julia

function within(s::Tuple, p::Tuple)::Union{Tuple{Int,Int},Nothing}
    if all((1, 1) .<= p .<= s)
        p
    else
        nothing
    end
end

function part1(s::Tuple, antennas::Dict{Char,Vector{Tuple{Int,Int}}})::Int
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

function part2(s::Tuple, antennas::Dict{Char,Vector{Tuple{Int,Int}}})::Int
    set = Set()
    for (_, l) in antennas
        for (i, p1) in enumerate(l)
            for (j, p2) in enumerate(l)
                if i < j
                    diff = p1 .- p2
                    d = (0, 0)
                    while (p = within(s, p2 .- d)) !== nothing
                        push!(set, p)
                        d = d .+ diff
                    end
                    d = (0, 0)
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

function run()::NamedTuple{(:part1, :part2),Tuple{Int,Int}}
    open("../data/2024/input-day08.txt", "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        s = size(m)
        antennas = Dict{Char,Vector{Tuple{Int,Int}}}()
        for i in axes(m, 1), j in axes(m, 2)
            c = m[i, j]
            if c != '.'
                l = get(antennas, c, Tuple{Int,Int}[])
                antennas[c] = push!(l, (i, j))
            end
        end
        (part1(s, antennas), part2(s, antennas))
    end
end

@time r = run()

println(r)
