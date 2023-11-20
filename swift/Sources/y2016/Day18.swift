//
//  Day18.swift
//
//
//  Created by 楢崎修二 on 2022/06/05.
//

import Foundation

var line = [false]

public func day18(_ data: String) {
  for ch in data.trimmingCharacters(in: CharacterSet.newlines) { line.append(ch == "^") }
  line.append(false)
  part1(line)
  part2(line)
}

func part1(_ line: [Bool]) { count(line: line, to: 40, label: 1) }
func part2(_ line: [Bool]) { count(line: line, to: 400000, label: 2) }

func count(line: [Bool], to: Int, label: Int) {
  var line = line
  var safes: Int = countSafe(in: line)
  func newGeneration(from: [Bool]) -> [Bool] {
    var to: [Bool] = [false]
    for ix in 1..<from.count - 1 {
      let b = from[ix - 1] != from[ix + 1]
      to.append(b)
    }
    to.append(false)
    return to
  }
  func countSafe(in vec: [Bool]) -> Int { vec.filter({ !$0 }).count - 2 }
  for _ in 1..<to {
    line = newGeneration(from: line)
    safes += countSafe(in: line)
  }
  print("Part\(label): \(safes)")
}

func printline(_ line: [Bool]) {
  for b in line { print(b ? "^" : ".", terminator: "") }
  print()
}
