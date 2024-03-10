// The Swift Programming Language
// https://docs.swift.org/swift-book
// import ArgumentParser
// import Foundation

public func day01(_ data: String) {
  let c = data.split(separator: "\n", omittingEmptySubsequences: false).split(separator: [])
  let d = c.map { $0.map { Int(String($0))! } }
  let e = d.map { $0.reduce(0) { (sum, cal) in sum + cal } }
  print("Part1: \(e.max()!)")
  print("Part2: \(e.sorted().reversed().prefix(3).reduce(0, +))")
}
