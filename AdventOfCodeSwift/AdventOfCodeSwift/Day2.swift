//
//  Day2.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/19.
//

import Foundation

let day2 = PuzzleDescripter(year: 2019, day: 2, title: "1202 Program Alarm", solver: Day2())

class Day2: Solver {
    var input: String?
    var inputFrom =  "input-y2019-day02"
    func reset() {
        guard let path = Bundle.main.path(forResource: inputFrom, ofType: "txt") else {
            fatalError("Couldn't load \(inputFrom).txt")
        }
        do {
            input = try String(contentsOfFile: path)
        } catch {
            fatalError("Couldn't read \(inputFrom).txt")
        }
    }
    func part1() -> String? {
       return nil
    }
    func part2() -> String? {
      return nil
    }
}
