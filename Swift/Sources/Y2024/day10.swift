import Utils

private func part1_aux(_ size: (Int, Int), _ grid: [[Int]], _ start: Pos) -> Int {
    let boundary = Pos.asBoundary(size)
    var to_visit: Set<Pos> = Set([start])
    var visited: Set<Pos> = Set()
    var goals: Set<Pos> = Set()
    while !to_visit.isEmpty {
        let pos = to_visit.removeFirst()
        visited.insert(pos)
        let h = grid[pos.y][pos.x]
        if h == 9 {
            goals.insert(pos)
            continue
        }
        for p in pos.neighbors4(bound: boundary) {
            if h + 1 == grid[p.y][p.x] && !visited.contains(p) {
                to_visit.insert(p)
            }
        }
    }
    return goals.count
}

private func part1(_ size: (Int, Int), _ grid: [[Int]], _ starts: [Pos]) -> Int {
    starts.reduce(0) { $0 + part1_aux(size, grid, $1) }
}
private func part2_aux(_ size: (Int, Int), _ grid: [[Int]], _ start: Pos) -> Int {
    let boundary = Pos.asBoundary(size)
    var to_visit: [Pos] = [start]
    var goals: Int = 0
    while !to_visit.isEmpty {
        let pos = to_visit.removeFirst()
        let h = grid[pos.y][pos.x]
        if h == 9 {
            goals += 1
            continue
        }
        for p in pos.neighbors4(bound: boundary) {
            let hh = grid[p.y][p.x]
            if h + 1 == hh {
                to_visit.append(p)
            }
        }
    }
    return goals
}

private func part2(_ size: (Int, Int), _ grid: [[Int]], _ starts: [Pos]) -> Int {
    starts.reduce(0) { $0 + part2_aux(size, grid, $1) }
}

public func day10(_ data: String) {
    let grid: [[Int]] = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map {
            Array($0).map { Int(($0 as Character).asciiValue! - Character("0").asciiValue!) }
        }
    let size = (grid.count, grid[0].count)
    var starts: [Pos] = []
    for (i, l) in grid.enumerated() {
        for (j, n) in l.enumerated() {
            if n == 0 {
                starts.append(Pos(y: i, x: j))
            }
        }
    }
    let sum1 = part1(size, grid, starts)
    let sum2 = part2(size, grid, starts)
    print("Part1: \(sum1)")
    print("Part2: \(sum2)")
}
