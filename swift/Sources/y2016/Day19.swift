//
//  Day19.swift
//
//
//  Created by 楢崎修二 on 2022/06/14.
//

import Foundation

class Day19 {
  let input = 3_014_603
  var line: [Bool] = []
  var inputFile: String = "../data/2016/input-day18.txt"
  var delimiter: String = "\n"
  func insert() {}
  init() {}

  func part1() {
    var next = [input]
    for i in 1...input {
      next.append(i + 1)
    }
    next[input] = 1
    var index = 1
    while next[index] != index {
      let i = next[next[index]]
      next[index] = i
      index = i
    }
    print("\(index)")
  }
  func part2() {
    var next = [input]
    for i in 1...input {
      next.append(i + 1)
    }
    next[input] = 1
    var remain = input
    var index = input / 2
    var dist = index
    while next[index] != index {
      let i = next[next[index]]
      next[index] = i
      remain -= 1
      if dist == remain / 2 {
        index = i
      } else {
        dist -= 1
      }
    }
    print("\(index)")
  }
}
