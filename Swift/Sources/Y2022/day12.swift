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

private func part1(_ grid: [[Int]], start: Pos, goal: Pos) -> Int {
    let boundary = Pos.boundary(of: grid)
    var visited: [Pos: Int] = [:]
    var toVisit: Heap<State> = [State(steps: 0, pos: start)]
    while let p = toVisit.popMin() {
        if visited[p.pos, default: p.steps + 1] <= p.steps {
            continue
        }
        visited[p.pos] = p.steps
        if p.pos == goal {
            continue
        }
        for q in p.pos.neighbors4(bound: boundary) {
            if grid[q] <= grid[p.pos] + 1 /* && p.cost < visited[q, default: p.cost + 1] */ {
                toVisit.insert(State(steps: p.steps + 1, pos: q))
            }
        }
    }
    return visited[goal, default: -1]
}

private func part2() -> Int {
    0
}

public func day12(_ data: String) {
    let lines: [[Character]] = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0) }
    let grid: [[Int]] = lines.map {
        $0.map {
            return switch $0 {
            case "S": 0
            case "E": 27
            default: Int($0.asciiValue! - Character("a").asciiValue! + 1)
            }
        }
    }
    var start = Pos.zero
    var end = Pos.zero
    for (i, l) in grid.enumerated() {
        for (j, c) in l.enumerated() {
            switch c {
            case 0: start = Pos(y: i, x: j)
            case 27: end = Pos(y: i, x: j)
            default: ()
            }
        }
    }
    let sum1 = part1(grid, start: start, goal: end)
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
