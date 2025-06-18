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
    var route: [State]
    var debugDescription: String {
        "\(pos)-\(dir)"
    }
    /// Return a new instance?
    func move(to: Pos) -> Raindeer? {
        let v = to - pos
        let r = route + [State(from: self)]
        if v == dir {
            return Raindeer(pos: to, dir: dir, cost: cost + 1, route: r)
        } else if v == dir.turnRight() {
            return Raindeer(pos: to, dir: dir.turnRight(), cost: cost + 1001, route: r)
        } else if v == dir.turnLeft() {
            return Raindeer(pos: to, dir: dir.turnLeft(), cost: cost + 1001, route: r)
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
    init(start: Pos) {
        self.pos = start
        self.dir = .east
    }
    init(from r: Raindeer) {
        self.pos = r.pos
        self.dir = r.dir
    }
}

private func part1(_ grid: [[Bool]], start: Pos, end: Pos) -> Int {
    let boundary: Pos = Pos.boundary(of: grid)
    var toVisit: Heap<Raindeer> = [Raindeer(pos: start, dir: .east, cost: 0, route: [])]
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
    fatalError()
}

private func part2(_ grid: [[Bool]], start: Pos, end: Pos) -> Int {
    let boundary: Pos = Pos.boundary(of: grid)
    let raindeer = Raindeer(pos: start, dir: .east, cost: 0, route: [State(start: start)])
    var toVisit: Heap<Raindeer> = [raindeer]
    var visited: [State: Int] = [:]
    var best: Int? = nil
    var bests: Set<State> = Set()
    while let r = toVisit.popMin() {
        if r.pos == end {
            if best ?? r.cost == r.cost {
                best = r.cost
                for p in r.route {
                    bests.insert(p)
                }
                bests.insert(State(from: r))
            }
            continue
        }
        let s = State(from: r)
        if visited[s, default: r.cost + 1] < r.cost {
            continue
        } else if visited[s, default: r.cost + 1] == r.cost && bests.contains(s) {
            // This is not performant. Since we use heap, candidates run in parallel.
            for p in r.route {
                bests.insert(p)
            }
            continue
        }
        visited[s] = r.cost
        for n in r.pos.neighbors4(bound: boundary) {
            if !grid[n], let s = r.move(to: n) {
                toVisit.insert(s)
            }
        }
    }
    return Set(bests.map { $0.pos }).count
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
    let sum2 = part2(grid, start: start, end: end)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
