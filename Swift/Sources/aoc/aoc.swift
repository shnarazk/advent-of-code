// The Swift Programming Language
// https://docs.swift.org/swift-book
import ArgumentParser
import Foundation
import Y2016
import Y2022
import Y2023
import Y2024

@main
struct Aoc: @preconcurrency ParsableCommand, Decodable {
    @Option(help: "year (4 digits)")
    public var year: Int = 2024

    @Argument(help: "day [1-25]")
    public var day: Int = 0

    @Option(help: "part [0-3]")
    public var part: Int = 0

    @Argument(help: "surfix part of file name for tests")
    public var test: String = ""

    public var dataFile: String {
        let d = String(format: "%02d", day)
        if test.isEmpty {
            return "../data/\(year)/input-day\(d).txt"
        } else {
            return "../data/\(year)/input-day\(d)-\(test).txt"
        }
    }

    @MainActor public func run() throws {
        print("\u{001B}[34mAoC: \(year)-\(day), file: \(dataFile)\u{001B}[0m")
        let data: String = try String(
            contentsOf: URL(fileURLWithPath: dataFile)
        )
        let beg = Date()
        switch year {
        case 2024:
            switch day {
            case 1: Y2024.day01(data)
            case 2: Y2024.day02(data)
            case 3: Y2024.day03(data)
            case 4: Y2024.day04(data)
            case 5: Y2024.day05(data)
            case 6: Y2024.day06(data)
            case 7: Y2024.day07(data)
            case 8: Y2024.day08(data)
            case 9: Y2024.day09(data)
            case 10: Y2024.day10(data)
            case 11: Y2024.day11(data)
            case 12: Y2024.day12(data)
            case 13: Y2024.day13(data)
            case 14: Y2024.day14(data)
            case 15: Y2024.day15(data)
            default: fatalError()
            }
        case 2023:
            switch day {
            case 1: Y2023.day01(data)
            case 2: Y2023.day02(data)
            case 3: Y2023.day03(data)
            case 4: Y2023.day04(data)
            case 5: Y2023.day05(data)
            case 6: Y2023.day06(data)
            case 7: Y2023.day07(data)
            case 8: Y2023.day08(data)
            case 9: Y2023.day09(data)
            case 10: Y2023.day10(data)
            case 11: Y2023.day11(data)
            default: fatalError()
            }
        case 2022:
            switch day {
            case 1: Y2022.day01(data)
            case 2: Y2022.day02(data)
            case 3: Y2022.day03(data)
            case 4: Y2022.day04(data)
            case 5: Y2022.day05(data)
            case 6: Y2022.day06(data)
            case 7: Y2022.day07(data)
            case 8: Y2022.day08(data)
            case 9: Y2022.day09(data)
            case 10: Y2022.day10(data)
            default: fatalError()
            }
        case 2016:
            switch day {
            case 18: Y2016.day18(data)
            case 19: Y2016.day19(data)
            case 22: Y2016.day22(data)
            default: fatalError()
            }
        default: fatalError()
        }
        let end = Date()
        let t = String(format: "%.2f", end.timeIntervalSince(beg) * 1000)
        print("\u{001B}[34m# Elapsed time: \(t) msec\u{001B}[0m")
    }
}
