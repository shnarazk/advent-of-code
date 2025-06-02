//
//  day07.swift
//  aoc
//
import Parsing

func kind(_ l: [UInt8]) -> Int {
    var set: [UInt8: UInt8] = [:]
    var numj: UInt8 = 0
    for c in l {
        if c == 0 {
            numj += 1
            continue
        }
        set[c, default: 0] += 1
    }
    if numj == 5 {
        return 7
    }
    let m: UInt8 = set.values.max()! + numj
    switch set.count {
        case 1: return 7
        case 2:
            if m == 4 {
                return 6
            } else if m == 3 {
                return 5
            } else {
                fatalError("Unreachable")
            }
        case 3:
            if m == 3 {
                return 4
            } else if m == 2 {
                return 3
            } else {
                fatalError("unreachable")
            }
        case 4: return 2
        case 5: return 1
        default: fatalError("unreachable")
    }
}

@DebugDescription
private struct Hand: Equatable {
    var cards: [Character]
    var bid: Int
    var debugDescription: String {
        "Hand(\(cards), \(bid))"
    }
    var kind1: (Int, [UInt8]) {
        let vals: [UInt8] = cards.map { switch $0 {
            case "T": 10
            case "J": 11
            case "Q": 12
            case "K": 13
            case "A": 14
            default: $0.asciiValue! - Character("0").asciiValue!
        }}
        return (kind(vals), vals)
    }
    var kind2: (Int, [UInt8]) {
        let vals: [UInt8] = cards.map { switch $0 {
            case "J": 0
            case "T": 10
            case "Q": 12
            case "K": 13
            case "A": 14
            default: $0.asciiValue! - Character("0").asciiValue!
        }}
        return (kind(vals), vals)
    }
}

func cmp(_ a: (Int, [UInt8]), _ b: (Int, [UInt8])) -> Bool {
    if a.0 == b.0 {
        for (x, y) in zip(a.1, b.1) {
            if x == y {
                continue
            }
            return x < y
        }
        fatalError("impossible")
    }
    return a.0 < b.0
}

private func part1(_ inputs: [Hand]) -> Int {
    return inputs.sorted(by: { cmp($0.kind1, $1.kind1) }).enumerated().reduce(0) {
        $0 + ($1.offset + 1) * $1.element.bid
    }
}

private func part2(_ inputs: [Hand]) -> Int {
    inputs.sorted(by: { cmp($0.kind2, $1.kind2) }).enumerated().reduce(0) {
        $0 + ($1.offset + 1) * $1.element.bid
    }
}

public func day07(_ data: String) {
    let hand_parser: some Parser<Substring, Hand> = Parse(input: Substring.self) {
        Prefix { !$0.isWhitespace }
        Prefix { $0.isWhitespace }
        Int.parser()
    }.map { Hand(cards: Array($0), bid: $2) }
    let parser: some Parser<Substring, [Hand]> = Many {
        hand_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let inputs = try parser.parse(data)
        let sum1 = part1(inputs)
        let sum2 = part2(inputs)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
