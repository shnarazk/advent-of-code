//
//  Day1.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation
import SwiftUI
import Charts

struct HistOfInt: Identifiable {
    let x: Int
    let y: Int
    var id: Int { get { return x } }
}

var day1 = Day1()

struct Day1: Solver, View, Identifiable, Hashable {
    var year: Int = 2019
    var day: Int = 1
    var title: String = "The Tyranny of the Rocket Equation"
    var inputFrom = "input-y2019-day01" // URL(string: "https://adventofcode.com/2019/day/1/input")!
    @State var input: String?
    @State var answerPart1: Int?
    @State var answerPart2: Int?
    @State var hist: [HistOfInt] = []
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
    func solvePart1() {
        reset()
        var total: Int = 0
        guard let input else { return }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else {fatalError("Something is wrong.") }
            total += n / 3 - 2
        }
        answerPart1 = total
    }
    func solvePart2() {
        reset()
        var total: Int = 0
        var hi: [Int: Int] = [:]
        guard let input else { return }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else { fatalError("Something is wrong.") }
            var fuel = n / 3 - 2
            var hist_count = 0
            while 0 < fuel {
                total += fuel
                fuel = fuel / 3 - 2
                hist_count += 1
            }
            hi[hist_count] = 1 + (hi[hist_count] ?? 0)
        }
        answerPart2 = total
        hist = hi.map { HistOfInt(x: $0, y: $1) }
    }
    var body: some View {
        VStack {
            PuzzlePageView(url: url)
            Section {
                Button("Run part 1") { solvePart1() }
                if let answer = answerPart1 {
                    Text("\(answer)")
                        .textSelection(.enabled)
                }
            }
            Section {
                Button("Run part 2") { solvePart2() }
                if let answer = answerPart2 {
                    Text("\(answer)")
                        .textSelection(.enabled)
                    Chart {
                        ForEach(hist) {
                            BarMark(
                                x: .value("iteration", $0.x),
                                y: .value("occurence", $0.y)
                            )
                        }
                    }
                }
            }
            Text("Year: \(year), Day: \(day): \(title), URL: \(url)")
                .font(.headline)
                .padding(.all)
            
        }
    }
}

struct Day1View_Previews: PreviewProvider {
    static var previews: some View {
        Day1()
    }
}
