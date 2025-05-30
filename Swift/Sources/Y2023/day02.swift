//
//  day02.swift
//  aoc
//

import Parsing

private struct Bag: Conversion {
    func apply(_ input: (String, Int)) throws -> Bag {
        Bag(color: input.0, amount: input.1)
    }
    func unapply(_ output: Bag) throws -> (String, Int) {
        (self.color, self.amount)
    }
    typealias Input = (String, Int)
    typealias Output = Bag

    var color: String
    var amount: Int
}

private func part1(_ data: [(Int, [[Bag]])]) -> Int {
    var sum = 0
    for (id, games) in data {
        var dic: [String: Int] = [:]
        for game in games {
            for b in game {
                dic[b.color] = max(dic[b.color, default: 0], b.amount)
            }
        }
        if 12 < dic["red", default: 0] || 13 < dic["green", default: 0] || 14 < dic["blue", default: 0] {
            continue
        }
        sum += id
    }
    return sum
}
private func part2(_ data: [(Int, [[Bag]])]) -> Int {
    var sum = 0
    for (_, games) in data {
        var dic: [String: Int] = [:]
        for game in games {
            for b in game {
                dic[b.color] = max(dic[b.color, default: 0], b.amount)
            }
        }
        var sub = 1
        for (_, n) in dic {
            sub *= n
        }
        sum += sub
    }
    return sum
}

public func day02(_ data: String) {
    let color_parser: some Parser<Substring, Bag> = Parse {
        Int.parser()
        " "
        Prefix { $0.isLetter }
    }
    .map { Bag(color: String($1), amount: $0) }
    let game_parser: some Parser<Substring, [Bag]> = Many {
        color_parser
    } separator: {
        ", "
    }
    let games_parser: some Parser<Substring, [[Bag]]> = Many {
        game_parser
    } separator: {
        "; "
    }
    let line_parser: some Parser<Substring, (Int, [[Bag]])> = Parse {
        "Game "
        Int.parser()
        ": "
        games_parser
    }
    let parser: some Parser<Substring, [(Int, [[Bag]])]> = Many {
       line_parser
    } separator: {
         "\n"
    } terminator: {
         "\n"
    }
    do {
        let data = try parser.parse(data)
        let sum1 = part1(data)
        print("Part 1: \(sum1)")
        let sum2 = part2(data)
        print("Part 2: \(sum2)")
    }
    catch {
        print(error)
    }
}
