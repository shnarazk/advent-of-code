//
//  Day1.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation

let day1 = PuzzleDescripter(year: 2019, day: 1, title: "The Tyranny of the Rocket Equation", solver: Day1())

class Day1: Solver {
    var input: String?
    var inputFrom = URL(string: "https://adventofcode.com/2019/day/1/input")!
    private let semaphore = DispatchSemaphore(value: 0)
    func reset() {
        self.visit(page: inputFrom)
    }
    func part1() -> String? {
        return "got input from \(inputFrom): \(input ?? "nil")"
    }
    func part2() -> String? { return nil }
    private func visit(page url: URL) {
        let task = URLSession.shared.dataTask(with: url) { data, response, error in
            guard
                let data = data,
                error == nil,
                let document = String(data: data, encoding: .utf8) else { return }
            self.input = document
            self.semaphore.signal()
        }
        task.resume()
        self.semaphore.wait()
    }
}
