//
//  day12.swift
//  aoc
//
import Collections
import Parsing
import Utils

@DebugDescription
private struct State: Comparable, Equatable, Hashable {
    let steps: Int
    let pos: Pos
    var debugDescription: String {
        "(\(pos), \(steps))"
    }
    static func == (lhs: State, rhs: State) -> Bool {
        lhs.steps == rhs.steps && lhs.pos == rhs.pos
    }
    static func < (lhs: State, rhs: State) -> Bool {
        lhs.steps < rhs.steps
    }
}

private func part1(_ height: [[Int]], start: Pos, goal: Pos) -> Int {
    let boundary = Pos.boundary(of: height)
    var visited: Set<Pos> = Set()
    var toVisit: Heap<State> = [State(steps: 0, pos: start)]
    while let p = toVisit.popMin() {
        if p.pos == goal {
            return p.steps
        }
        if visited.contains(p.pos) {
            continue
        }
        visited.insert(p.pos)
        for q in p.pos.neighbors4(bound: boundary) {
            if height[q] <= height[p.pos] + 1 && !visited.contains(q) {
                toVisit.insert(State(steps: p.steps + 1, pos: q))
            }
        }
    }
    fatalError()
}

private func part2() -> Int {
    0
}

public func day12(_ data: String) {
    let lines: [[Character]] = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    var start = Pos.zero
    var goal = Pos.zero
    let grid: [[Int]] = lines.enumerated().map { (i, l) in
        l.enumerated().map { (j, c) in
            switch c {
            case "S":
                start = Pos(y: i, x: j)
                return 0
            case "E":
                goal = Pos(y: i, x: j)
                return 25
            default:
                return Int(c.asciiValue! - Character("a").asciiValue!)
            }
        }
    }
    let sum1 = part1(grid, start: start, goal: goal)
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
