//
//  Day19.swift
//
//
//  Created by 楢崎修二 on 2022/06/14.
//

public func day19(_ data: String) {
  let input = 3_014_603
  func part1() {
    var next = [input]
    next.append(contentsOf: Array(2...input + 1))
    next[input] = 1
    var index = 1
    while next[index] != index {
      let i = next[next[index]]
      next[index] = i
      index = i
    }
    print("Part 2: \(index)")
  }
  func part2() {
    var next = [input]
    next.append(contentsOf: Array(2...input + 1))
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
    print("Part 2: \(index)")
  }
  part1()
  part2()
}
