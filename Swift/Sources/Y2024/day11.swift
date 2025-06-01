//
//  day11.swift
//  aoc
//
import Parsing

@DebugDescription
private struct Stone: Hashable {
    var mark: Int
    var level: Int
    var debugDescription: String {
        return "\(mark), \(level)"
    }
    var dividable: (Int, Int)? {
        var n = mark
        var digits = 1
        while 10 <= n {
            n /= 10
            digits += 1
        }
        if digits % 2 == 0 {
            var n = mark
            var a = 0
            var b = 0
            var base = 1
            for _ in 0..<digits / 2 {
                a += (n % 10) * base
                n /= 10
                base *= 10
            }
            base = 1
            for _ in 0..<digits / 2 {
                b += (n % 10) * base
                n /= 10
                base *= 10
            }
            return (a, b)
        } else {
            return nil
        }
    }
}

private func count(_ stone: Stone, _ cache: inout [Stone: Int], _ depth: Int) -> Int {
    if stone.level == depth {
        return 1
    }
    if let cached = cache[stone] {
        return cached
    }
    var n = 0
    if stone.mark == 0 {
        n = count(Stone(mark: 1, level: stone.level + 1), &cache, depth)
    } else if let (a, b) = stone.dividable {
        n += count(Stone(mark: a, level: stone.level + 1), &cache, depth)
        n += count(Stone(mark: b, level: stone.level + 1), &cache, depth)
    } else {
        n = count(Stone(mark: stone.mark * 2024, level: stone.level + 1), &cache, depth)
    }
    cache[stone] = n
    return n
}

private func part1(_ stones: [Int]) -> Int {
    var cache: [Stone: Int] = [:]
    return stones.reduce(0) { $0 + count(Stone(mark: $1, level: 0), &cache, 25) }
}

private func part2(_ stones: [Int]) -> Int {
    var cache: [Stone: Int] = [:]
    return stones.reduce(0) { $0 + count(Stone(mark: $1, level: 0), &cache, 75) }
}

public func day11(_ data: String) {
    let parser: some Parser<Substring, [Int]> = Many {
        Int.parser()
    } separator: {
        " "
    } terminator: {
        "\n"
    }
    do {
        let nums = try parser.parse(data)
        let sum1 = part1(nums)
        let sum2 = part2(nums)
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
