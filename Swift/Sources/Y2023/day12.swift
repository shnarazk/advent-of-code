//
//  day12.swift
//  aoc
//
import Parsing

private enum Kind {
    case F
    case T
    case Q
}

private struct Key: Hashable {
    let a: [Kind]
    let b: Int
}

private func matchSequenceAux(string: [Kind], target: [Int], dict: inout [Key: Int])
    -> Int
{
    switch (string.isEmpty, target.isEmpty) {
    case (true, true): return 1
    case (false, true): return string.allSatisfy { $0 != .T } ? 1 : 0
    case (true, false): return 0
    default: ()
    }
    if string.count < target.reduce(0, +) {
        return 0
    }
    let beg: Kind = string[0]
    let ends_at: Int = string.firstIndex { $0 != beg } ?? string.count
    switch beg {
    case .F:
        return matchSequence(string: Array(string[1...]), target: target, dict: &dict)
    case .T:
        if target[0] < ends_at {
            return 0
        } else if target[0] == ends_at {
            if target[0] == string.count {
                return 1
            } else {
                return matchSequence(
                    string: Array(string[(target[0] + 1)...]),
                    target: Array(target[1...]),
                    dict: &dict
                )
            }
        } else {
            if ((ends_at..<target[0]).allSatisfy { i in
                i < string.count && string[i] != .F
                    && (target[0] == string.count || string[target[0]] != .T)
            }) {
                if string.count < target[0] + 1 {
                    return target.count == 1 ? 1 : 0
                } else {
                    return matchSequence(
                        string: Array(string[(target[0] + 1)...]),
                        target: Array(target[1...]),
                        dict: &dict
                    )
                }
            } else {
                return 0
            }
        }
    case .Q:
        var v = string
        v[0] = .F
        let c0 = matchSequence(string: v, target: target, dict: &dict)
        v[0] = .T
        let c1 = matchSequence(string: v, target: target, dict: &dict)
        return c0 + c1
    }
}

private func matchSequence(string: [Kind], target: [Int], dict: inout [Key: Int]) -> Int {
    let key: Key = Key(a: Array(string), b: target.count)
    if let c = dict[key] {
        return c
    }
    let x = matchSequenceAux(string: string, target: target, dict: &dict)
    dict[key] = x
    return x
}

private func part1(_ inputs: [([Kind], [Int])]) -> Int {
    inputs.map {
        var dict = [Key: Int]()
        return matchSequence(string: $0.0, target: $0.1, dict: &dict)
    }
    .reduce(0) { $0 + $1 }
}

private func part2(_ inputs: [([Kind], [Int])]) -> Int {
    inputs.map {
        var dict = [Key: Int]()
        let s5: [Kind] = Array(Array(repeating: $0.0, count: 5).joined(separator: [.Q]))
        let t5: [Int] = Array(Array(repeating: $0.1, count: 5).joined())
        return matchSequence(string: s5, target: t5, dict: &dict)
    }
    .reduce(0) { $0 + $1 }
}

public func day12(_ data: String) {
    let line: some Parser<Substring, ([Kind], [Int])> = Parse {
        Prefix { $0 != " " }.map {
            Array($0).map {
                switch $0 {
                case ".": Kind.F
                case "#": Kind.T
                case "?": Kind.Q
                default: fatalError()
                }
            }
        }
        " "
        Many(1...) {
            Int.parser()
        } separator: {
            ","
        }
    }
    let parser: some Parser<Substring, [([Kind], [Int])]> = Many(1...) {
        line
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
        fatalError()
    }
}
