module Geometry

export Dim2, Dim2_zero, Dim2_unit
export Dim2_up, Dim2_right, Dim2_down, Dim2_left
export within, turn_right, neighbors4

const Dim2 = CartesianIndex{2}

const Dim2_zero::Dim2 = CartesianIndex(0, 0)
const Dim2_unit::Dim2 = CartesianIndex(1, 1)
const Dim2_up::Dim2 = CartesianIndex(-1, 0)
const Dim2_right::Dim2 = CartesianIndex(0, 1)
const Dim2_down::Dim2 = CartesianIndex(1, 0)
const Dim2_left::Dim2 = CartesianIndex(0, -1)

function within(pos::Dim2, boundary::Dim2)::Union{Dim2,Nothing}
    # The following does not work well due to axis oredr
    # Dim2_unit <= pos <= boundary
    # Even this does not.
    # if all(collect(Tuple(Dim2_unit)) .<= collect(Tuple(pos)) .<= collect(Tuple(boundary)))
    all(a -> Dim2_unit[a] <= pos[a] <= boundary[a], 1:2) ? pos : nothing
end

# println([Dim2_zero .<= Dim2(1, 1),
#          Dim2(1, 1) .<= Dim2(1, 0),
#          Dim2(1, 0) .<= Dim2(0, 0),
#          Dim2(0, 1) .<= Dim2(0, 0),
#          Dim2(0, 0) .<= Dim2(0, 0),
#          ])
# println(within(Dim2(1, 2), Dim2(3, 5)))
# println(within(Dim2(1, 2), Dim2(0, 0)))
# println(Dim2(1, 2) + Dim2(3, 5))

"""Turn clockwise"""
function turn_right(d::Dim2)::Dim2
    get(
        Dict(
            Dim2_up => Dim2_right,
            Dim2_right => Dim2_down,
            Dim2_down => Dim2_left,
            Dim2_left => Dim2_up),
        d,
        Dim2_zero)
end

# println(turn_right(Dim2_right))

function neighbors4(pos::Dim2, boundary::Dim2)::Vector{Dim2}
    dirs = [Dim2_up, Dim2_right, Dim2_down, Dim2_left]
    map(d -> within(pos + d, boundary), dirs) |> l -> filter(e -> e !== nothing, l)
end

# print("n4 1: ")
# println(neighbors4(Dim2(1, 1), Dim2(3, 3)))
# print("n4 2: ")
# println(neighbors4(Dim2(1, 2), Dim2(4, 4)))
# xx = collect(Tuple(Dim2_unit)) <= collect(Tuple(Dim2(2, 0))) # <= Dim2(5,5)
# xx = within(Dim2(0, 2), Dim2(5,5))
# println("the problem is $xx")
# error()
# end
end
