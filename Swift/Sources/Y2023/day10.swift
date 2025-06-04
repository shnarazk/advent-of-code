//
//  day10.swift
//  aoc
//
import Parsing
import Utils

@DebugDescription
private struct Cursor {
    var pos: Pos
    var dir: Pos
    var steps: Int = 0
    var debugDescription: String {
        "(\(pos), \(dir), \(steps))"
    }
    func goForward(_ grid: [[Character]]) -> Cursor? {
        switch (grid[pos], dir) {
        case ("|", .north): Cursor(pos: pos + .north, dir: dir, steps: steps + 1)
        case ("|", .south): Cursor(pos: pos + .south, dir: dir, steps: steps + 1)
        case ("-", .east): Cursor(pos: pos + .east, dir: dir, steps: steps + 1)
        case ("-", .west): Cursor(pos: pos + .west, dir: dir, steps: steps + 1)
        case ("L", .west): Cursor(pos: pos + .north, dir: .north, steps: steps + 1)
        case ("L", .south): Cursor(pos: pos + .east, dir: .east, steps: steps + 1)
        case ("J", .east): Cursor(pos: pos + .north, dir: .north, steps: steps + 1)
        case ("J", .south): Cursor(pos: pos + .west, dir: .west, steps: steps + 1)
        case ("7", .east): Cursor(pos: pos + .south, dir: .south, steps: steps + 1)
        case ("7", .north): Cursor(pos: pos + .west, dir: .west, steps: steps + 1)
        case ("F", .north): Cursor(pos: pos + .east, dir: .east, steps: steps + 1)
        case ("F", .west): Cursor(pos: pos + .south, dir: .south, steps: steps + 1)
        default: nil
        }
    }
    static func goOn(start: Pos, dir: Pos, grid: [[Character]]) -> Cursor? {
        var c = Cursor(pos: start + dir, dir: dir)
        while let next = c.goForward(grid) {
            if next.pos == start {
                return next
            }
            c = next
        }
        return nil
    }
}

private func part1(_ grid: [[Character]]) -> Int {
    let start: Pos =
        if let (i, s) = grid.enumerated().first(
            where: {
                $0.1.contains("S")
            })
        {
            Pos(y: i, x: s.firstIndex(where: { $0 == "S" })!)
        } else {
            fatalError(#function)
        }
    if let v = Cursor.goOn(start: start, dir: .north, grid: grid) {
        return (v.steps + 1) / 2
    }
    if let h = Cursor.goOn(start: start, dir: .east, grid: grid) {
        return (h.steps + 1) / 2
    }
    fatalError()
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
        // assert(input.allSatisfy { $0.allSatisfy { $0 != "S" } })
        let sum1 = part1(input)
        let sum2 = part2(input)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
