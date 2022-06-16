//
//  Day22.swift
//  
//
//  Created by 楢崎修二 on 2022/06/12.
//

import Foundation
import Regex

class Day22: PuzzleSolver {
    var line: [(Int, Int, Int, Int)] = []
    var inputFile: String = "../data/2016/input-day22.txt"
    var delimiter: String = "\n"

    init() {
        insert()
        // example()
    }
    func example() {
        line = []
    }
    func insert() {
        if #available(macOS 13.0, *) {
            let parse: Regex = /dev/grid/node-x(\d+)-y(\d+) +(\d+)T +(\d+)T +(\d+)T +(\d+)%$/
        } else {
            // Fallback on earlier versions
        }
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
    func part1() {
      
    }
    func part2() {
    }
}
