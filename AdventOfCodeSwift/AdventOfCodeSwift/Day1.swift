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
    var inputFrom =  "input-y2019-day01" // URL(string: "https://adventofcode.com/2019/day/1/input")!
    private let semaphore = DispatchSemaphore(value: 0)
    func reset() {
        // self.visit(page: inputFrom)
        // input = Bundle.main.path(forResource: inputFrom, ofType: "txt")
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
        var total: Int = 0
        // return "got input from \(inputFrom): \(input ?? "nil")"
        guard let input else { return nil }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else {
                fatalError("Something is wrong.")
            }
            total += n / 3 - 2
        }
        return "\(total)"
    }
    func part2() -> String? {
        var total: Int = 0
        guard let input else { return nil }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else {
                fatalError("Something is wrong.")
            }
            var fuel = n / 3 - 2
            while 0 < fuel {
                total += fuel
                fuel = fuel / 3 - 2
            }
        }
        return "\(total)"
    }
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
