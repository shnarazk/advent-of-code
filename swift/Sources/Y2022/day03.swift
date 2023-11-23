// The Swift Programming Language
// https://docs.swift.org/swift-book
// import ArgumentParser
// import Foundation

public func day03(_ data: String) {
  let lines = Array(data.split(separator: "\n", omittingEmptySubsequences: true))
  let Z = Character("Z").asciiValue!
  let A = Character("@").asciiValue!
  let a = Character("`").asciiValue!
  func part1(_ lines: [String.SubSequence]) {
    let lines = lines
    var sum = 0
    for l in lines {
      let l = Array(l)
      let half = l.count / 2
      let setA = Set(l.prefix(through: half - 1))
      let setB = Set(l.suffix(from: half))
      let ch = setA.intersection(setB).first!.asciiValue!
      if Z < ch { sum += Int(ch - a) } else { sum += Int(ch - A + 26) }
    }
    print("Part1: \(sum)")
  }

  func part2(_ lines: [String.SubSequence]) {
    var lines = lines
    var sum = 0
    while !lines.isEmpty {
      let target = lines[0..<3].map { Set(Array($0)) }
      let ch = target[0].intersection(target[1]).intersection(target[2]).first!.asciiValue!
      if Z < ch { sum += Int(ch - a) } else { sum += Int(ch - A + 26) }
      lines = Array(lines.dropFirst(3))
    }
    print("Part2: \(sum)")
  }
  part1(lines)
  part2(lines)
}
