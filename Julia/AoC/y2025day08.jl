using AoC, AoC.Parser, ParserCombinator

🔎position = (🔎int + E"," + 🔎int + E"," + 🔎int) |> (n -> n)
🔎positions = Repeat(🔎position + 🔎newline)

function run()::ANS
    part1, part2 = 0, 0
    boxes::Vector{Vector{Int}} =
        parse_one(read(open(datafile(2025, 8), "r"), String), 🔎positions)
    dists::Vector{Tuple{Int,Int,Int}} = []
    for (i, box1) in enumerate(boxes)
        for (j, box2) in Iterators.drop(enumerate(boxes), i)
            diff = abs.(box1 .- box2)
            dist = diff .* diff
            push!(dists, (sum(dist), i, j))
        end
    end
    sort!(dists)
    to_group::Vector{Union{Int,Nothing}} = fill(nothing, length(boxes))
    groups = []
    next_gid = 1
    if length(boxes) == 1000
        limit = 1000
    else
        limit = 10
    end
    num_groups = 0
    for (iteration, (_, i, j)) in enumerate(dists)
        if to_group[i] == nothing
            gi = nothing
        else
            g = something(to_group[i], -1)
            while groups[g] != 0
                g = groups[g]
            end
            gi = g
        end
        if to_group[j] == nothing
            gj = nothing
        else
            g = something(to_group[j], -1)
            while groups[g] != 0
                g = groups[g]
            end
            gj = g
        end
        if gi == nothing && gj == nothing
            to_group[i] = next_gid
            to_group[j] = next_gid
            push!(groups, 0)
            next_gid += 1
            num_groups += 1
        elseif gi == nothing && gj != nothing
            to_group[i] = gj
        elseif gi != nothing && gj == nothing
            to_group[j] = gi
        elseif gi != gj
            groups[gi] = next_gid
            groups[gj] = next_gid
            push!(groups, 0)
            next_gid += 1
            num_groups -= 1
        end
        if iteration == limit
            effective_groups::Dict{Int,Int} = Dict()
            for gi in to_group
                if gi == nothing
                    continue
                end
                g = something(gi, -1)
                while groups[g] != 0
                    g = groups[g]
                end
                effective_groups[g] = 1 + get(effective_groups, g, 0)
            end
            vals = sort(collect(values(effective_groups)); rev = true)
            part1 = vals[1] * vals[2] * vals[3]
        end
        if num_groups == 1 && all(o -> o != nothing, to_group)
            part2 = boxes[i][1] * boxes[j][1]
            break
        end
    end
    (part1, part2)
end

@time println(run())
