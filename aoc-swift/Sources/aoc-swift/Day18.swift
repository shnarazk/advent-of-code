//
//  Day18.swift
//  
//
//  Created by 楢崎修二 on 2022/06/05.
//

import Foundation

class Day18: PuzzleSolver {
    var line: [Bool] = []
    var inputFile: String = "../data/2016/input-day18.txt"
    var delimiter: String = "\n"

    init() {
        insert()
    }
    func insert() {
        do {
            let input: String = try String(contentsOfFile: inputFile)
            line = [false]
            for ch in input { line.append(ch == "^") }
            line.append(false)
            print("Line: \(line)")
        } catch {
            print("Not found \(inputFile)")
        }
    }
    func part1() {
        print(line.count)
        print(countSafe(in: line))
//        print(newGeneration(from: line))
    }
    func part2() {}
    func newGeneration(from: [Bool]) -> [Bool] {
        var to: [Bool] = [false]
        for ix in 1..<from.count - 1 {
            let b =
                ( from[ix - 1] &&  from[ix] && !from[ix + 1]) ||
                (!from[ix - 1] &&  from[ix] &&  from[ix + 1]) ||
                ( from[ix - 1] && !from[ix] && !from[ix + 1]) ||
                (!from[ix - 1] && !from[ix] &&  from[ix + 1])
            to.append(b)
        }
        to.append(false)
        return to
    }
    func countSafe(in vec: [Bool]) -> Int {
        vec.filter({ $0 }).count
    }
}
