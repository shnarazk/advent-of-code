typealias Cursor = (pos: (Int, Int), dir: (Int, Int))

func turn_right(_ dir: (Int, Int)) -> (Int, Int) {
    switch dir {
    case (-1, 0): (0, 1)
    case (0, 1): (1, 0)
    case (1, 0): (0, -1)
    case (0, -1): (-1, 0)
    default: (0, 0)
    }
}

func add(_ a: (Int, Int), _ b: (Int, Int)) -> (Int, Int) {
    (a.0 + b.0, a.1 + b.1)
}

func add(_ a: Cursor) -> (Int, Int) {
    add(a.pos, a.dir)
}

func within(_ me: (Int, Int), in size: (Int, Int)) -> (Int, Int)? {
    if 0 <= me.0 && me.0 < size.0 && 0 <= me.1 && me.1 < size.1 {
        me
    } else {
        nil
    }
}
private func part1(_ size: (Int, Int), _ mirrors: Set<[Int]>, _ start: (Int, Int))
    -> Int
{
    var passing: Set<[Int]> = Set()
    var now: Cursor = (pos: start, dir: (-1, 0))
    passing.insert([now.pos.0, now.pos.1])
    while within(add(now), in: size) != nil {
        var pos = add(now.pos, now.dir)
        var dir = now.dir
        if mirrors.contains([pos.0, pos.1]) {
            dir = turn_right(dir)
            pos = add(now.pos, dir)
        }
        now = (pos, dir)
        // print(now)
        passing.insert([now.pos.0, now.pos.1])

    }

    return passing.count
}

private func part2(_ size: (Int, Int), _ mirror: Set<[Int]>, _ start: (Int, Int))
    -> Int
{
    0
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
    let sum1 = part1(size, mirrors, start)
    let sum2 = part2(size, mirrors, start)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
