//
//  File.swift
//  
//
//  Created by 楢崎修二 on 2022/06/05.
//

import Foundation

class Day18: PuzzleSolver {
    var inputFile: String = "../data/2016/input-day18.txt"
    var delimiter: String = "\n"

    func insert() {
        do {
            let input = try String(contentsOfFile: inputFile)
            print(input)
        } catch {
            print("Not found \(inputFile)")
        }
    }

    func part1() {

        self.insert()
        print(0)
    }
}
