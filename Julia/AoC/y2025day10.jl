using AoC, AoC.Parser, ParserCombinator, JuMP, HiGHS

🔎indicator = E"[" + p"[.#]+" + E"] "
🔎button = E"(" + Repeat(🔎int + E",") + 🔎int + E")" |> b -> Int.(b) #  [b]
🔎buttons = Repeat(🔎button + E" ") |> bs -> bs
🔎requirement = E"{" + Repeat(🔎int + E",") + 🔎int + E"}" |> r -> Int.(r)
🔎line = 🔎indicator + 🔎buttons + 🔎requirement

function run()::ANS
    part1, part2 = 0, 0
    for line in eachline(open(datafile(2025, 10), "r"))
        parsed = parse_one(line, 🔎line)
        indicators = Int.(collect(parsed[1]) .== '#')
        buttons::Vector{Vector{Int}} = parsed[2]
        requirement::Vector{Int} = parsed[3]
        num_buttons = length(buttons)
        num_lights = length(requirement)
        m = zeros(Int, num_lights, num_buttons)
        for (bi, button) in enumerate(buttons)
            for lj in button
                m[lj + 1, bi] = 1
            end
        end
        # println(requirement)
        part1 += solve_equation1(num_buttons, num_lights, m, indicators)
        part2 += solve_equation2(num_buttons, num_lights, m, requirement)
        # println(buttons)
    end
    (part1, part2)
end

function solve_equation1(num_buttons::Int, num_lights::Int, m::Matrix, goal::Vector{Int})::Int
    to_visit::Set{Vector{Int}} = Set()
    push!(to_visit, zeros(num_buttons))
    while length(to_visit) > 0
        next::Set{Vector{Int}} = Set()
        for state in to_visit
            is::Vector{Int} = zeros(num_lights)
            for (bi, n) in enumerate(state)
                for li = 1:num_lights
                    is[li] += m[li, bi] * n
                end
            end
            if is .% 2 == goal
                return sum(state)
            end
            for i = 1:num_buttons
                s = copy(state)
                s[i] += 1
                push!(next, s)
            end
        end
        to_visit = next
    end
    0
end

function solve_equation2(num_buttons::Int, num_lights::Int, m::Matrix, goal::Vector{Int})::Int
    model = Model(HiGHS.Optimizer)
    set_optimizer_attribute(model, "output_flag", false)
    @variable(model, v[1:num_buttons] >= 0, Int)
    for i in 1:num_lights
        @constraint(model, sum(m[i,j] * v[j] for j in 1:num_buttons) == goal[i])
    end
    @objective(model, Min, sum(v))

    optimize!(model)

    if termination_status(model) == MOI.OPTIMAL
        sum(round.(value.(v)))
    else
        println("No feasible integer solution found")
        0
    end
end

@time println(run())
