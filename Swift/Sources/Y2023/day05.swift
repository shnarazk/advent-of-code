//
//  day05.swift
//  aoc
//
import Parsing

typealias Rule = (to: Int, from: Int, len: Int)

private func mapTo(_ rules: [Rule], _ p: Int) -> Int {
    for rule in rules {
        if rule.from <= p && p < rule.from + rule.len {
            return p + (rule.to - rule.from)
        }
    }
    return p
}

private func part1(_ stages: [(String, String, [Rule])], _ src: [Int]) -> Int {
    stages.reduce(src) { seq, stage in seq.map { mapTo(stage.2, $0) } }.min()!
}

private func part2() -> Int {
    0
}

public func day05(_ data: String) {
    // Many accepts empty int sequence!kk
    let ints: some Parser<Substring, [Int]> = Parse {
        Int.parser()
        " "
        Many {
            Int.parser()
        } separator: {
            " "
        }
    }.map { [$0] + $1 }
    let rule: some Parser<Substring, Rule> = Parse {
        Int.parser()
        " "
        Int.parser()
        " "
        Int.parser()
    }.map { (to: $0, from: $1, len: $2) }

    let seeds_parser: some Parser<Substring, [Int]> = Parse {
        "seeds: "
        ints
    }
    let block_parser: some Parser<Substring, (String, String, [Rule])> = Parse {
        Prefix { $0 != "-" }
        "-to-"
        Prefix { $0 != " " }
        " map:\n"
        Many {
            rule
        } separator: {
            "\n"
        }
    }.map { (String($0), String($1), $2) }
    let parser: some Parser<Substring, ([Int], [(String, String, [Rule])])> = Parse {
        seeds_parser
        "\n\n"
        Many {
            block_parser
        } terminator: {
            "\n"
        }
    }
    do {
        let input = try parser.parse(data)
        let sum1 = part1(input.1, input.0)
        let sum2 = part2()
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
