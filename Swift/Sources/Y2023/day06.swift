//
//  day06.swift
//  aoc
//

import Parsing
import Utils

private struct Setting {
    var time: Int
    var distance: Int
    var ways_to_win: Int {
        // Since the answers are calculated by multiplication,
        // we can asssume the maximum product must be a solution.
        // It's at `time / 2`.
        var beg = 0
        var end = time / 2
        while 1 < end - beg {
            let med = (beg + end) / 2
            if distance < med * (time - med) {
                end = med
            } else {
                beg = med
            }
        }
        let start = end
        assert(distance < start * (time - start))
        end = time - 1
        beg = time / 2
        while 1 < end - beg {
            let med = (beg + end) / 2
            if distance < med * (time - med) {
                beg = med
            } else {
                end = med
            }
        }
        let finish = beg
        // assert(distance < finish * (time - finish))
        return finish - start + 1
    }
}

private func part1(_ settings: [Setting]) -> Int {
    settings.reduce(1) { $0 * $1.ways_to_win }
}

private func part2() -> Int {
    0
}

public func day06(_ data: String) {
    let ints_parser: some Parser<Substring, [Int]> = Parse {
        Prefix { !$0.isNumber }
        Many {
            Int.parser()
            Prefix { $0 == " " }
        }.map { $0.map { $0.0 } }
    }.map { $1 }
    let parser: some Parser<Substring, ([Int], [Int])> = Parse {
        ints_parser
        "\n"
        ints_parser
        "\n"
    }
    do {
        let (time, distance) = try parser.parse(data)
        let settings: [Setting] = zip(time, distance).map { Setting(time: $0.0, distance: $0.1) }
        let sum1 = part1(settings)
        let t = settings.reduce(0) { append_digits($0, $1.time) }
        let d = settings.reduce(0) { append_digits($0, $1.distance) }
        let sum2 = part1([Setting(time: t, distance: d)])
        print("Part 1: \(sum1)")
        print("Part 2: \(sum2)")
    } catch {
        print(error)
    }
}
