module Geometry

export Dim2, Dim2_zero, Dim2_unit
export within

"""
    Index type for 2 Dimentional space
"""
const Dim2 = CartesianIndex{2}

const Dim2_zero::Dim2 = CartesianIndex(0, 0)
const Dim2_unit::Dim2 = CartesianIndex(1, 1)

# module Dir
# import Geometry: Dim2

# export zero, unit, U, R, D, L, dirs, turn_right

# const zero::Dim2 = CartesianIndex(0, 0)
# const unit::Dim2 = CartesianIndex(1, 1)

# """
#   up = (-1, 0)
# """
# const U::Dim2 = CartesianIndex(-1, 0)

# """
#   right = (0, 1)
# """
# const R::Dim2 = CartesianIndex(0, 1)

# """
#   down = (1, 0)
# """
# const D::Dim2 = CartesianIndex(1, 0)

# """
#   left = (0, -1)
# """
# const L::Dim2 = CartesianIndex(0, -1)

# const dirs = [U, R, D, L]

# """Turn clockwise"""
# function turn_right(d::Dim2)::Dim2
#     get(Dict(U => R, R => D, D => L, L => U), d, zero)
# end

# end

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


# println(turn_right(Dim2_right))


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
