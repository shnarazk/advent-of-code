//
//  day10.swift
//  aoc
//
import Parsing
import Utils

private struct Cursor {
    var pos: Pos
    var dir: Pos
    func goForward(_ grid: [[Character]]) -> Cursor {
        switch (grid[pos], dir) {
        case ("|", .north): Cursor(pos: pos + .north, dir: dir)
        case ("|", .south): Cursor(pos: pos + .south, dir: dir)
        case ("-", .east): Cursor(pos: pos + .east, dir: dir)
        case ("-", .west): Cursor(pos: pos + .west, dir: dir)
        case ("L", .west): Cursor(pos: pos + .north, dir: .north)
        case ("L", .south): Cursor(pos: pos + .east, dir: .east)
        case ("J", .east): Cursor(pos: pos + .north, dir: .north)
        case ("J", .south): Cursor(pos: pos + .west, dir: .west)
        case ("7", .east): Cursor(pos: pos + .south, dir: .south)
        case ("7", .north): Cursor(pos: pos + .west, dir: .west)
        case ("F", .north): Cursor(pos: pos + .east, dir: .east)
        case ("F", .west): Cursor(pos: pos + .south, dir: .south)
        default: fatalError()
        }
    }
}

private func part1(_ input: [[Character]]) -> Int {
    let start: Pos =
        if let (i, s) = input.enumerated().first(
            where: {
                !$0.1.allSatisfy { $0 == "." }
            })
        {
            Pos(y: i, x: s.firstIndex(where: { $0 != "." })!)
        } else {
            fatalError(#function)
        }
    var cursor: Cursor = Cursor(pos: start, dir: Pos.east)
    return 0
}

private func part2(_ input: [[Character]]) -> Int {
    0
}

public func day10(_ data: String) {
    let parser: some Parser<Substring, [[Character]]> = Many {
        Prefix {
            $0 != "\n"
        }.map { Array($0) }
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
