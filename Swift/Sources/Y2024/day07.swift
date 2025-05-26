//
//  day07.swift
//  aoc

import Parsing

func part1(_ line: (Int, [Int])) -> Int {
    var values: Set<Int> = Set()
    for n in line.1 {
        if values.isEmpty {
            values.insert(n)
            continue
        }
        var tmp: Set<Int> = Set()
        for s in values {
            let x = s + n
            if x <= line.0 {
                tmp.insert(x)
            }
            let y = s * n
            if y <= line.0 {
                tmp.insert(y)
            }
        }
        values = tmp
    }
    if values.contains(line.0) {
        return line.0
    } else {
        return 0
    }
}

public func day07(_ data: String) {
    let elements_parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    }
    let line_parser: some Parser<Substring, (Int, [Int])> = Parse(
        input: Substring.self
    ) {
        Int.parser()
        ": "
        elements_parser
    }
    let parser: some Parser<Substring, [(Int, [Int])]> = Many {
        line_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let data = try parser.parse(data)
        print("\(data)")
        let sum1 = data.reduce(into: 0) { acc, line in acc += part1(line) }
        print("Part1: \(sum1)")
    } catch {
        print(error)
    }
}
