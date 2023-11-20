// The Swift Programming Language
// https://docs.swift.org/swift-book
import ArgumentParser
import Foundation
import Y2016
import Y2022

@main
struct Aoc: ParsableCommand, Decodable {
  @Option(help: "year (4 digits)")
  public var year: Int = 2022

  @Argument(help: "day [1-25]")
  public var day: Int = 0

  @Argument(help: "part [0-3]")
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

  public func run() throws {
    print("\u{001B}[34mAoC: \(year)-\(day), part: \(part), file: \(dataFile)\u{001B}[0m")
    let data: String = try String(contentsOf: URL(fileURLWithPath: dataFile))
    switch year {
    case 2023:
      switch day {
      // case 1: Y2022.day01(data)
      // case 2: Y2022.day02(data)
      default: fatalError()
      }
    case 2022:
      switch day {
      case 1: Y2022.day01(data)
      case 2: Y2022.day02(data)
      default: fatalError()
      }
    case 2016:
      switch day {
      case 18: Y2016.day18(data)
      // case 2: Y2016.day02(data)
      default: fatalError()
      }
    default: fatalError()
    }
  }
}
