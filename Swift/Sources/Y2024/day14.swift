//
//  day14.swift
//  aoc
//
import Parsing
import Utils

@DebugDescription
private struct Robot {
    let pos: Pos
    let vec: Pos
    var debugDescription: String {
        "(\(pos.y): \(pos.x)) (\(vec.y), \(vec.x))"
    }
}

private func part1(robots: [Robot], boundary: Pos) -> Int {
    let time = 100
    let map =
        robots
        // map to the final positions
        .map {
            ((($0.vec * time + $0.pos) % boundary) + boundary) % boundary
        }
        // map to region map
        .reduce((0, 0, 0, 0)) {
            if boundary.y / 2 == $1.y || boundary.x / 2 == $1.x {
                $0
            } else {
                switch (boundary.y / 2 < $1.y, boundary.x / 2 < $1.x) {
                case (false, false): ($0.0 + 1, $0.1, $0.2, $0.3)
                case (false, true): ($0.0, $0.1 + 1, $0.2, $0.3)
                case (true, false): ($0.0, $0.1, $0.2 + 1, $0.3)
                case (true, true): ($0.0, $0.1, $0.2, $0.3 + 1)
                }
            }
        }
    // convert to the product
    return map.0 * map.1 * map.2 * map.3
}

private func part2() -> Int {
    0
}

public func day14(_ data: String) {
    let is_test = Array(data.split(separator: "\n", omittingEmptySubsequences: true)).count == 12
    let boundary: Pos = is_test ? Pos(y: 7, x: 11) : Pos(y: 103, x: 101)
    let robot: some Parser<Substring, Robot> = Parse {
        "p="
        Int.parser()
        ","
        Int.parser()
        " v="
        Int.parser()
        ","
        Int.parser()
    }.map { Robot(pos: Pos(y: $1, x: $0), vec: Pos(y: $3, x: $2)) }
    let parser: some Parser<Substring, [Robot]> = Many {
        robot
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(robots: input, boundary: boundary)
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
