//
//  Day18.swift
//
//
//  Created by 楢崎修二 on 2022/06/05.
//

import Foundation

class Day18 {
  var line: [Bool] = []
  var inputFile: String = "../data/2016/input-day18.txt"
  var delimiter: String = "\n"

  init() {
    insert()
    // example()
  }
  func example() {
    line = [false]
    for ch in ".^^.^.^^^^" {
      line.append(ch == "^")
    }
    line.append(false)
  }
  func insert() {
    do {
      let input: String = try String(contentsOfFile: inputFile)
      line = [false]
      for ch in input.trimmingCharacters(in: CharacterSet.newlines) { line.append(ch == "^") }
      line.append(false)
    } catch {
      print("Not found \(inputFile)")
    }
  }
  func part1() {
    print("0 \(countSafe(in: line)): ", terminator: "")
    printline()
    var safes: Int = countSafe(in: line)
    for i in 1..<40 {
      line = newGeneration(from: line)
      safes += countSafe(in: line)
      print("\(i) \(countSafe(in: line)): ", terminator: "")
      printline()
    }
    print("safe places: \(safes)")
  }
  func part2() {
    print("0 \(countSafe(in: line)): ", terminator: "")
    printline()
    var safes: Int = countSafe(in: line)
    for _ in 1..<400000 {
      line = newGeneration(from: line)
      safes += countSafe(in: line)
      //            print("\(i) \(countSafe(in: line)): ", terminator: "")
      //            printline()
    }
    print("safe places: \(safes)")
  }
  func newGeneration(from: [Bool]) -> [Bool] {
    var to: [Bool] = [false]
    for ix in 1..<from.count - 1 {
      //            let b =
      //                ( from[ix - 1] &&  from[ix] && !from[ix + 1]) ||
      //                (!from[ix - 1] &&  from[ix] &&  from[ix + 1]) ||
      //                ( from[ix - 1] && !from[ix] && !from[ix + 1]) ||
      //                (!from[ix - 1] && !from[ix] &&  from[ix + 1])
      let b = from[ix - 1] != from[ix + 1]
      to.append(b)
    }
    to.append(false)
    return to
  }
  func countSafe(in vec: [Bool]) -> Int {
    vec.filter({ !$0 }).count - 2
  }
  func printline() {
    for b in line {
      print(b ? "^" : ".", terminator: "")
    }
    print()
  }
}
