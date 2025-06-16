//
//  day12.swift
//  aoc
//
import Parsing
import Utils

private struct State: Equatable, Hashable {
    let cost: Int
    let pos: Pos
}

private func part1(_ grid: [[Int]], start: Pos, end: Pos) -> Int {
    let boundary = Pos.boundary(of: grid)
    var toVisit: Set<State> = Set([State(cost:0, pos: start)])
    var visited: Set<State> = Set()
    while let p = toVisit.popFirst() {
        if p.pos == end {
            return 0
        }
        visited.insert(p)
        for q in p.pos.neighbors4(bound: boundary) {
            if !visited.contains(State(cost: p.cost + 1, pos: q)) {
                toVisit.insert(State(cost: p.cost + 1, pos: q))
            }
        }
    }
    return 0
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
            case "S": 1000
            case "E": 2000
            default: Int($0.asciiValue! - Character("a").asciiValue!)
            }
        }
    }
    var start = Pos.zero
    var end = Pos.zero
    for (i, l) in grid.enumerated() {
        for (j, c) in l.enumerated() {
            switch c {
            case 1000: start = Pos(y: i, x: j)
            case 2000: end = Pos(y: i, x: j)
            default: ()
            }
        }
    }
    let sum1 = part1(grid, start: start, end: end)
    let sum2 = part2()
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
