//
//  day07.swift
//  aoc
//
import Parsing

@DebugDescription
private struct Hand: Equatable {
    var cards: [Character]
    var bid: Int
    var debugDescription: String {
        "Hand(\(cards), \(bid))"
    }
    var rank1: Int {
        0
    }
    var rank2: Int {
        0
    }
}

private func part1(_ inputs: [Hand]) -> Int {
    inputs.sorted(by: { $0.rank1 > $1.rank1 }).enumerated().reduce(0) {
        $0 + ($1.offset + 1) * $1.element.bid
    }
}

private func part2(_ inputs: [Hand]) -> Int {
    inputs.sorted(by: { $0.rank2 > $1.rank2 }).enumerated().reduce(0) {
        $0 + ($1.offset + 1) * $1.element.bid
    }
}

public func day07(_ data: String) {
    let hand_parser: some Parser<Substring, Hand> = Parse(input: Substring.self) {
        Prefix { !$0.isWhitespace }
        Prefix { $0.isWhitespace }
        Int.parser()
    }.map { Hand(cards: Array($0).sorted(), bid: $2) }
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
