//
//  day13.swift
//  aoc
//
import Parsing
import Utils

@DebugDescription
private struct Claw {
    let buttonA: Pos
    let buttonB: Pos
    let prize: Pos
    var debugDescription: String {
        "(\(buttonA) + \(buttonB) => \(prize))"
    }
    var solve: Int {
        if buttonA.x * buttonB.y != buttonA.y * buttonB.x {
            let tmp1 = abs(buttonA.x * buttonB.y - buttonA.y * buttonB.x)
            let tmp2 = abs(buttonB.y * prize.x - buttonB.x * prize.y)
            let tmp3 = abs(buttonA.x * prize.y - buttonA.y * prize.x)
            let i = tmp2 / tmp1
            let im = tmp2 % tmp1
            let j = tmp3 / tmp1
            let jm = tmp3 % tmp1
            return (im == 0 && jm == 0) ? 3 * i + j : 0
        } else {
            return 0
        }
    }
}

private func part1(_ data: [Claw]) -> Int {
    data.reduce(0) { $0 + $1.solve }
}

private func part2(_ data: [Claw]) -> Int {
    data.reduce(0) {
        let tmp = Claw(
            buttonA: $1.buttonA,
            buttonB: $1.buttonB,
            prize: $1.prize + 10_000_000_000_000
        )
        return $0 + tmp.solve
    }
}

public func day13(_ data: String) {
    let line_parser: some Parser<Substring, Pos> = Parse {
        Prefix {
            $0 != ":"
        }
        ": X"
        OneOf {
            "+"
            "="
        }
        Int.parser()
        ", Y"
        OneOf {
            "+"
            "="
        }
        Int.parser()
    }
    .map { Pos(y: $2, x: $1) }
    let claw: some Parser<Substring, Claw> = Parse {
        line_parser
        "\n"
        line_parser
        "\n"
        line_parser
    }.map { Claw(buttonA: $0, buttonB: $1, prize: $2) }

    let parser: some Parser<Substring, [Claw]> = Many {
        claw
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(input)
        let sum2 = part2(input)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
