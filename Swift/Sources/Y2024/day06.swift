import Utils

private typealias Cursor = (pos: Pos, dir: Pos)

private func add(_ a: Cursor) -> Pos {
    a.pos + a.dir
}

private func part1(
    _ size: (Int, Int),
    _ mirrors: Set<Pos>,
    _ start: Cursor,
    _ passing: Set<Pos>,
    _ looping: Set<[Pos]>
)
    -> Int?
{
    let boundary = Pos.asBoundary(size)
    var passing = passing
    var looping = looping
    var now: Cursor = start
    passing.insert(now.pos)
    looping.insert([now.pos, now.dir])
    while var pos = add(now).within(boundary) {
        var dir = now.dir
        if mirrors.contains(pos) {
            dir = dir.turn_right()
            pos = now.pos + dir
            if mirrors.contains(pos) {
                dir = dir.turn_right()
                pos = now.pos + dir
            }
        }
        if looping.contains([pos, dir]) {
            return nil
        }
        now = (pos, dir)
        passing.insert(now.pos)
        looping.insert([now.pos, now.dir])
    }
    return passing.count
}

private func part2(
    _ size: (Int, Int),
    _ mirrors: Set<Pos>,
    _ start: Cursor,
    _ passing: Set<Pos>,
    _ looping: Set<[Pos]>
)
    -> Int
{
    let boundary = Pos.asBoundary(size)
    var count = 0
    var passing = passing
    var looping = looping
    var now: Cursor = start
    passing.insert(now.pos)
    looping.insert([now.pos, now.dir])
    while var pos = add(now).within(boundary) {
        var dir = now.dir
        if mirrors.contains(pos) {
            dir = dir.turn_right()
            pos = now.pos + dir
            if mirrors.contains(pos) {
                dir = dir.turn_right()
                pos = now.pos + dir
            }
        }
        do {
            var m = mirrors
            m.insert(pos)
            if !passing.contains(pos)
                && part1(size, m, (pos: now.pos, dir: dir), passing, looping) == nil
            {
                count += 1
            }
        }
        now = (pos, dir)
        passing.insert(now.pos)
        looping.insert([now.pos, now.dir])
    }
    return count
}

public func day06(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let size = (lines.count, lines[0].count)
    var mirrors: Set<Pos> = Set()
    var start: Pos = Pos.zero
    for (i, l) in lines.enumerated() {
        for (j, c) in l.enumerated() {
            if c == "#" {
                mirrors.insert(Pos(y: i, x: j))
            } else if c == "^" {
                start = Pos(y: i, x: j)
            }
        }
    }
    let now: Cursor = (pos: start, dir: Pos.north)
    let passing: Set<Pos> = Set([now.pos])
    let looping: Set<[Pos]> = Set([[now.pos, now.dir]])
    let sum1 = part1(size, mirrors, now, passing, looping)!
    let sum2 = part2(size, mirrors, now, passing, looping)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
