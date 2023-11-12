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

  @Argument(help: "data file")
  public var data: String? = nil

  public func run() throws {
    print("Hello, world!")
    print("day: \(day), part: \(part)")
    if let dataFile = data {
      let data: String? = try String(contentsOf: URL(fileURLWithPath: dataFile))
      if let data = data { f(data) }
    }
  }
}

func f(_ data: String) {
  let c = data.split(separator: "\n", omittingEmptySubsequences: false).split(separator: [])
  let d = c.map { $0.map { Int(String($0))! } }
  let e = d.map {
    $0.reduce(0) { (sum, cal) in
      return
        sum + cal
    }
  }
  print(e.max()!)
}
