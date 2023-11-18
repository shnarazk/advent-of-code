// The Swift Programming Language
// https://docs.swift.org/swift-book
import ArgumentParser
import Foundation

@main
struct Aoc: ParsableCommand, Decodable {
  @Argument(help: "day [1-25]")
  public var day: Int = 0

  @Argument(help: "part [0-3]")
  public var part: Int = 0

  public var dataFile: String {
    let d = String(format: "%02d", day)
    return "../../data/2022/input-day\(d).txt"
  }

  public func run() throws {
    print("day: \(day), part: \(part), file: \(dataFile)")
    if day == 1 {
      let data: String? = try String(contentsOf: URL(fileURLWithPath: dataFile))
      if let data = data { day01(data) }
    }
  }
}
