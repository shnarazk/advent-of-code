//
//  day09.swift
//  aoc
//
import Parsing

private func diff(_ src: [Int]) -> [Int] {
    (0..<(src.count - 1)).map { src[$0 + 1] - src[$0] }
}

private func converged(_ src: [Int]) -> Int? {
    src.allSatisfy { $0 == src[0] } ? src[0] : nil
}

private func solution1(_ data: [Int]) -> Int {
    converged(data) ?? data.last! + solution1(diff(data))
}

private func solution2(_ data: [Int]) -> Int {
    converged(data) ?? data.first! - solution2(diff(data))
}

private func part1(_ data: [[Int]]) -> Int {
    data.reduce(0) { $0 + solution1($1) }
}

private func part2(_ data: [[Int]]) -> Int {
    data.reduce(0) { $0 + solution2($1) }
}

public func day09(_ data: String) {
    let line_parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    }
    let parser: some Parser<Substring, [[Int]]> = Many {
        line_parser
    } separator: {
        "\n"
    }
    do {
        let input = try parser.parse(data).filter { !$0.isEmpty }
        let sum1 = part1(input)
        let sum2 = part2(input)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
