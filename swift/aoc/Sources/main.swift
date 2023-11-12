// The Swift Programming Language
// https://docs.swift.org/swift-book
import ArgumentParser

@main
struct Aoc: ParsableCommand, Decodable {
  @Argument(help: "day [1-25]")
  public var day: Int = 0

  @Argument(help: "part [0-3]")
  public var part: Int = 0

  public func run() throws {
    print("Hello, world!")
    print("day: \(day), part: \(part)")
  }
}
