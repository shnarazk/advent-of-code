module Dirs


export Dir, Up, Right, Down, Left, pos, turn

# Juliaにはろくな列挙型の機能がないことがわかった🤷
@enum Dir begin
    Up
    Right
    Down
    Left
end

"""Turn clockwise"""
function turn(d::Dir)::Dir
    get(
        Dict(Up => Right, Right => Down, Down => Left, Left => Up),
        d,
        nothing)
end

function pos(d::Dir)::Vector{Int}
    get(
        Dict(Up => [-1, 0], Right => [0, 1], Down => [1, 0], Left => [0, -1]),
        d,
        [0, 0]
    )
end

end
