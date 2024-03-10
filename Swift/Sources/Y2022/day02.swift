// The Swift Programming Language
// https://docs.swift.org/swift-book
// import ArgumentParser
// import Foundation

public func day02(_ data: String) {
  let c = data.split(separator: "\n", omittingEmptySubsequences: false)
  var sum = 0
  for s in c {
    let v = switch s {
    case "A X" : 1 + 3
    case "A Y" : 2 + 6
    case "A Z" : 3 + 0
    case "B X" : 1 + 0
    case "B Y" : 2 + 3
    case "B Z" : 3 + 6
    case "C X" : 1 + 6
    case "C Y" : 2 + 0
    case "C Z" : 3 + 3
    default: 0
    }
    sum += v
  }
  print("Part1: \(sum)") 
  sum = 0
  for s in c {
    let v = switch s {
    case "A X": 3 + 0
    case "A Y": 1 + 3
    case "A Z": 2 + 6
    case "B X": 1 + 0
    case "B Y": 2 + 3
    case "B Z": 3 + 6
    case "C X": 2 + 0
    case "C Y": 3 + 3
    case "C Z": 1 + 6
    default: 0
    }
    sum += v
  }
  print("Part2: \(sum)") 
}
