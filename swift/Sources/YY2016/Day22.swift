//
//  Day22.swift
//
//
//  Created by 楢崎修二 on 2022/06/12.
//

import Foundation

func day22() {
  var line: [(Int, Int, Int, Int)] = []
  let inputFile: String = "../data/2016/input-day22.txt"

  func insert() {
    // let parse = try Regex(#"dev/grid/node-x(\d+)-y(\d+) +(\d+)T +(\d+)T +(\d+)T +(\d+)%$"#))
    // if #available(macOS 13.0, *) {
    // } else {
    //     // Fallback on earlier versions
    // }
    do {
      let input: String = try String(contentsOfFile: inputFile)
      line = []
      for _ in input.split(separator: "\n") {
        line.append((0, 0, 0, 0))
      }
    } catch {
      print("Not found \(inputFile)")
    }
  }
}
