import Utils

private typealias Cursor = (pos: (Int, Int), dir: (Int, Int))

private func turn_right(_ dir: (Int, Int)) -> (Int, Int) {
    switch dir {
    case (-1, 0): (0, 1)
    case (0, 1): (1, 0)
    case (1, 0): (0, -1)
    case (0, -1): (-1, 0)
    default: (0, 0)
    }
}

private func add(_ a: (Int, Int), _ b: (Int, Int)) -> (Int, Int) {
    (a.0 + b.0, a.1 + b.1)
}

private func add(_ a: Cursor) -> (Int, Int) {
    add(a.pos, a.dir)
}

private func part1(
    _ size: (Int, Int),
    _ mirrors: Set<[Int]>,
    _ start: Cursor,
    _ passing: Set<[Int]>,
    _ looping: Set<[Int]>
)
    -> Int?
{
    var passing = passing
    var looping = looping
    var now: Cursor = start
    passing.insert([now.pos.0, now.pos.1])
    looping.insert([now.pos.0, now.pos.1, now.dir.0, now.dir.1])
    while within(add(now), in: size) != nil {
        var pos = add(now.pos, now.dir)
        var dir = now.dir
        if mirrors.contains([pos.0, pos.1]) {
            dir = turn_right(dir)
            pos = add(now.pos, dir)
            if mirrors.contains([pos.0, pos.1]) {
                dir = turn_right(dir)
                pos = add(now.pos, dir)
            }
        }
        if looping.contains([pos.0, pos.1, dir.0, dir.1]) {
            return nil
        }
        now = (pos, dir)
        // print(now)
        passing.insert([now.pos.0, now.pos.1])
        looping.insert([now.pos.0, now.pos.1, now.dir.0, now.dir.1])
    }
    return passing.count
}

private func part2(
    _ size: (Int, Int),
    _ mirrors: Set<[Int]>,
    _ start: Cursor,
    _ passing: Set<[Int]>,
    _ looping: Set<[Int]>
)
    -> Int
{
    var count = 0
    var passing = passing
    var looping = looping
    var now: Cursor = start
    passing.insert([now.pos.0, now.pos.1])
    looping.insert([now.pos.0, now.pos.1, now.dir.0, now.dir.1])
    while within(add(now), in: size) != nil {
        var pos = add(now.pos, now.dir)
        var dir = now.dir
        if mirrors.contains([pos.0, pos.1]) {
            dir = turn_right(dir)
            pos = add(now.pos, dir)
            if mirrors.contains([pos.0, pos.1]) {
                dir = turn_right(dir)
                pos = add(now.pos, dir)
            }
        }
        do {
            var m = mirrors
            m.insert([pos.0, pos.1])
            let tmp = (pos: now.pos, dir: dir)
            if !passing.contains([pos.0, pos.1])
                && part1(size, m, tmp, passing, looping) == nil
            {
                count += 1
            }
        }
        now = (pos, dir)
        passing.insert([now.pos.0, now.pos.1])
        looping.insert([now.pos.0, now.pos.1, now.dir.0, now.dir.1])
    }
    return count
}

public func day06(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let size = (lines.count, lines[0].count)
    var mirrors: Set<[Int]> = Set()
    var start: (Int, Int) = (0, 0)
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c == "#" {
                mirrors.insert([i, j])
            } else if c == "^" {
                start = (i, j)
            }
        }
    }
    let now: Cursor = (pos: start, dir: (-1, 0))
    let passing: Set<[Int]> = Set([[now.pos.0, now.pos.1]])
    let looping: Set<[Int]> = Set([[now.pos.0, now.pos.1, now.dir.0, now.dir.1]])
    let sum1 = part1(size, mirrors, now, passing, looping)!
    let sum2 = part2(size, mirrors, now, passing, looping)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
