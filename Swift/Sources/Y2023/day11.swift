//
//  day11.swift
//  aoc
//
import Utils

func totalDistance(set m: Set<Pos>, from pos: Pos) -> Int {
    m.map { ($0 - pos).l1Norm() }.reduce(0, +)
}

func scaleUp(_ m: [[Bool]], y: [Int], x: [Int], to scale: Int) -> Set<Pos> {
    var transY = y
    var index = 0
    for i in transY.indices {
        if transY[i] == 1 {
            transY[i] = index
            index += 1
        } else {
            index += scale
        }
    }
    var transX = x
    index = 0
    for j in transX.indices {
        if transX[j] == 1 {
            transX[j] = index
            index += 1
        } else {
            index += scale
        }
    }
    var s: Set<Pos> = Set()
    for (i, row) in m.enumerated() {
        for (j, b) in row.enumerated() {
            if b {
                s.insert(Pos(y: transY[i], x: transX[j]))
            }
        }
    }
    return s
}

private func solve(_ m: [[Bool]], y: [Int], x: [Int], scale: Int) -> Int {
    let s = scaleUp(m, y: y, x: x, to: scale)
    return s.map { totalDistance(set: s, from: $0) }.reduce(0, +) / 2
}

public func day11(_ data: String) {
    let input = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
        .map { Array($0).map { $0 == "#" } }
    var transY: [Int] = Array(repeating: 0, count: input.count)
    var transX: [Int] = Array(repeating: 0, count: input[0].count)
    for (i, l) in input.enumerated() {
        for (j, b) in l.enumerated() {
            if b {
                transX[j] = 1
                transY[i] = 1
            }
        }
    }
    let sum1 = solve(input, y: transY, x: transX, scale: 2)
    let sum2 = solve(input, y: transY, x: transX, scale: 1_000_000)
    print("Part 1: \(sum1)")
    print("Part 2: \(sum2)")
}
