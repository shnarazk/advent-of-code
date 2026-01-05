using AoC, AoC.Geometry, AoC.Dir

const Cursor = NamedTuple{(:pos, :dir),Tuple{Dim2,Dim2}}

function part1(m::Matrix{Char})::Int
    boundary = Dim2(size(m)...)
    cursor::Cursor = (pos = findfirst(==('^'), m), dir = Dir.U)
    passed = Set([cursor.pos])
    while within(cursor.pos + cursor.dir, boundary) !== nothing
        pos = cursor.pos + cursor.dir
        dir = cursor.dir
        if m[pos] == '#'
            dir = turn_right(dir)
            pos = cursor.pos + dir
            @assert m[pos] != '#'
        end
        cursor = (pos = pos, dir = dir)
        push!(passed, pos)
    end
    length(passed)
end

function is_loop(m::Matrix{Char}, cursor::Cursor, passed::Set)::Bool
    m = copy(m)
    boundary = Dim2(size(m)...)
    m[cursor.pos+cursor.dir] = '#'
    passed = copy(passed)
    while within(cursor.pos + cursor.dir, boundary) !== nothing
        pos = cursor.pos + cursor.dir
        dir = cursor.dir
        if m[pos] == '#'
            dir = turn_right(dir)
            pos = cursor.pos + dir
            if m[pos] == '#'
                dir = turn_right(dir)
                pos = cursor.pos + dir
            end
        end
        cursor = (pos = pos, dir = dir)
        if cursor in passed
            return true
        else
            push!(passed, cursor)
        end
    end
    false
end

function part2(m::Matrix{Char})::Int
    boundary = Dim2(size(m)...)
    loops = Set()
    cursor::Cursor = (pos = findfirst(==('^'), m), dir = Dir.U)
    passed::Set{Cursor} = Set([cursor])
    while within(cursor.pos + cursor.dir, boundary) !== nothing
        pos = cursor.pos + cursor.dir
        dir = cursor.dir
        if m[pos] == '#'
            dir = turn_right(dir)
            pos = cursor.pos + dir
            @assert m[pos] != '#'
            cursor = (pos = cursor.pos, dir = dir)
        end
        if all(c -> c.pos != pos, passed) && is_loop(m, cursor, passed)
            push!(loops, pos)
        end
        cursor = (pos = pos, dir = dir)
        push!(passed, cursor)
    end
    length(loops)
end

function run()::ANS
    open(datafile(2024, 6), "r") do file
        lines = String.(eachline(file)) |> s -> filter(!isempty, s)
        m = hcat(map(collect, lines)...) |> permutedims |> Matrix
        (part1(m), part2(m))
    end
end

@time println(run())
