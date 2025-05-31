using AoC, AoC.Geometry

function part1(s::Dim2, antennas::Dict{Char,Vector{Dim2}})::Int
    set = Set()
    for (_, l) in antennas
        for (i, p1) in enumerate(l)
            for (j, p2) in enumerate(l)
                if i < j
                    diff = p1 .- p2
                    if (p = within(p2 .- diff, s)) !== nothing
                        push!(set, p)
                    end
                    if (p = within(p1 .+ diff, s)) !== nothing
                        push!(set, p)
                    end
                end
            end
        end
    end
    length(set)
end

function part2(s::Dim2, antennas::Dict{Char,Vector{Dim2}})::Int
    set = Set()
    for (_, l) in antennas
        for (i, p1) in enumerate(l)
            for (j, p2) in enumerate(l)
                if i < j
                    diff = p1 .- p2
                    d = Dim2_zero
                    while (p = within(p2 .- d, s)) !== nothing
                        push!(set, p)
                        d = d .+ diff
                    end
                    d = Dim2_zero
                    while (p = within(p1 .+ d, s)) !== nothing
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
        antennas = Dict{Char,Vector{Dim2}}()
        for ix in CartesianIndices(m)
            c = m[ix]
            if c != '.'
                l = get(antennas, c, Dim2[])
                antennas[c] = push!(l, ix)
            end
        end
        (part1(s, antennas), part2(s, antennas))
    end
end

@time println(run())
