module Dir

include("Geometry.jl")
using .Geometry

export U, R, D, L, dirs, turn_right, neighbors4

"""
  up = (-1, 0)
"""
const U::Dim2 = CartesianIndex(-1, 0)

"""
  right = (0, 1)
"""
const R::Dim2 = CartesianIndex(0, 1)

"""
  down = (1, 0)
"""
const D::Dim2 = CartesianIndex(1, 0)

"""
  left = (0, -1)
"""
const L::Dim2 = CartesianIndex(0, -1)

const dirs = [U, R, D, L]

"""Turn clockwise"""
function turn_right(d::Dim2)::Dim2
    get(Dict(U => R, R => D, D => L, L => U), d, zero)
end

function neighbors4(pos::Dim2, boundary::Dim2)::Vector{Dim2}
    map(d -> within(pos + d, boundary), Dir.dirs) |> l -> filter(e -> e !== nothing, l)
end

end
