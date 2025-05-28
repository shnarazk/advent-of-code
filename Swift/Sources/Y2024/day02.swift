//
//  day02.swift
//  aoc
//

import Parsing

private func part1(_ seq: [Int]) -> Int {
    var inc = true
    var dec = true
    if seq.count < 2 {
        return 1
    }
    for i in 0..<seq.count - 1 {
        if 3 < abs(seq[i + 1] - seq[i]) {
            return 0
        }
        inc = inc && seq[i] < seq[i + 1]
        dec = dec && seq[i] > seq[i + 1]
        if !(inc || dec) {
            return 0
        }
    }
    // print(seq)
    return inc || dec ? 1 : 0
}

private func part2(_ seq: [Int]) -> Int {
    if part1(seq) == 1 {
        return 1
    }
    for i in 0..<seq.count {
        var s = seq
        s.remove(at: i)
        if part1(s) == 1 {
            return 1
        }
    }
    return 0
}

public func day02(_ data: String) {
    let sequence_parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    }

    let parser: some Parser<Substring, [[Int]]> = Many {
        sequence_parser
    } separator: {
        "\n"
    }

    do {
        let lines = try parser.parse(data[...]).filter { !$0.isEmpty }
        let sum1 = lines.map(part1).reduce(0, +)
        let sum2 = lines.map(part2).reduce(0, +)
        print("Part1: \(sum1)")
        print("Part2: \(sum2)")
    } catch {
        print("\(error)")
    }
}
