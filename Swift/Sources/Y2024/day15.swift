//
//  day15.swift
//  aoc
//
import Parsing

private func part1() -> Int {
    0
}

private func part2() -> Int {
    0
}

public func day15(_ data: String) {
    let grid: some Parser<Substring, [[Character]]> = Parse {
        Many {
            Prefix { ["#", ".", "O", "@"].contains($0) }
                .map { Array(String($0)) }
        } separator: {
            "\n"
            //        } terminator: {
            //            "\n\n"
        }
    }
    let moves: some Parser<Substring, [Character]> = Parse {
        Prefix { ["^", ">", "v", "<", "\n"].contains($0) }
            .map { Array($0.filter { $0 != "\n" }) }
    }
    let parser: some Parser<Substring, ([[Character]], [Character])> = Parse {
        grid
        moves
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1()
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
        fatalError()
    }
}
