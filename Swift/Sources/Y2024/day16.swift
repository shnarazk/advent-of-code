//
//  day16.swift
//  aoc
//
import Collections
import Parsing
import Utils

@DebugDescription
private struct Raindeer: Comparable, Hashable {
    var pos: Pos
    var dir: Pos
    var cost: Int
    var debugDescription: String {
        "\(pos)-\(dir)"
    }
    /// Return a new instance?
    func move(to: Pos) -> Raindeer? {
        let v = to - pos
        if v == dir {
            return Raindeer(pos: to, dir: dir, cost: cost + 1)
        } else if v == dir.turnRight() {
            return Raindeer(pos: to, dir: dir.turnRight(), cost: cost + 1001)
        } else if v == dir.turnLeft() {
            return Raindeer(pos: to, dir: dir.turnLeft(), cost: cost + 1001)
        } else {
            return nil
        }
    }
    static func < (lhs: Raindeer, rhs: Raindeer) -> Bool {
        lhs.cost < rhs.cost
    }
}

private struct State: Hashable {
    let pos: Pos
    let dir: Pos
    init(from r: Raindeer) {
        self.pos = r.pos
        self.dir = r.dir
    }
}

private func part1(_ grid: [[Bool]], start: Pos, end: Pos) -> Int {
    let boundary: Pos = Pos.boundary(of: grid)
    var toVisit: Heap<Raindeer> = [Raindeer(pos: start, dir: .east, cost: 0)]
    var visited: Set<State> = Set()
    while let r = toVisit.popMin() {
        if r.pos == end {
            return r.cost
        }
        let s = State(from: r)
        if visited.contains(s) {
            continue
        }
        visited.insert(s)
        for n in r.pos.neighbors4(bound: boundary) {
            if !grid[n], let s = r.move(to: n) {
                toVisit.insert(s)
            }
        }
    }
    return 0
}

private func part2() -> Int {
    0
}

public func day16(_ data: String) {
    let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
    var start: Pos = Pos.zero
    var end: Pos = Pos.zero
    let grid: [[Bool]] = lines.enumerated().map { (i, l) in
        l.enumerated().map { (j, c) in
            switch c {
            case "S":
                start = Pos(y: i, x: j)
                return false
            case "E":
                end = Pos(y: i, x: j)
                return false
            case ".":
                return false
            case "#":
                return true
            default:
                fatalError()
            }
        }
    }
    let sum1 = part1(grid, start: start, end: end)
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
