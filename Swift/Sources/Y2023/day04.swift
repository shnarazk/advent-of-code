//
//  File.swift
//  aoc
//

import Foundation
import Parsing

@DebugDescription
private struct Card {
    let id: Int
    let winningNumbers: Set<Int>
    let numbers: [Int]
    var debugDescription: String {
        "Card \(id): \(numbers)"
    }
    var matchPoints: Int {
        Int(powl(2, Double(numbers.filter { winningNumbers.contains($0) }.count - 1)))
    }
    var matches: Int {
        numbers.filter { winningNumbers.contains($0) }.count
    }
}

private func part1(_ cards: [Card]) -> Int {
    cards.reduce(0) { $0 + $1.matchPoints }
}

private func part2(_ cards: [Card]) -> Int {
    var pile: [(Int, Card)] = cards.map { (1, $0) }
    var numCards = 0
    while !pile.isEmpty {
        let first = pile.removeFirst()
        numCards += first.0
        for i in 0..<first.1.matches {
            if i < pile.count {
                pile[i].0 += first.0
            }
        }
    }
    return numCards
}

public func day04(_ data: String) {
    let card_parser: some Parser<Substring, Card> = Parse {
        "Card"
        Prefix { !$0.isNumber }
        Int.parser()
        Prefix { !$0.isNumber }
        Many {
            Int.parser()
        } separator: {
            Prefix { $0 == " " }
        } terminator: {
            " | "
        }
        Prefix { !$0.isNumber }
        Many {
            Int.parser()
        } separator: {
            Prefix { $0 == " " }
        }
    }.map { Card(id: $1, winningNumbers: Set($3), numbers: $5) }
    let parser: some Parser<Substring, [Card]> = Many {
        card_parser
    } separator: {
        "\n"
    } terminator: {
        "\n"
    }
    do {
        let cards = try parser.parse(data)
        let sum1 = part1(cards)
        print("Part 1: \(sum1)")
        let sum2 = part2(cards)
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
