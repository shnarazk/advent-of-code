//
//  Day1.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation
import SwiftUI

struct Day1: Solver, View, Identifiable, Hashable {
    var year: Int = 2019
    var day: Int = 1
    var title: String = "The Tyranny of the Rocket Equation"
    var inputFrom = "input-y2019-day01" // URL(string: "https://adventofcode.com/2019/day/1/input")!
    @State var input: String?
    @State var answerPart1: Int?
    @State var answerPart2: Int?
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
        var total: Int = 0
        guard let input else { return }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else {fatalError("Something is wrong.") }
            total += n / 3 - 2
        }
        answerPart1 = total
    }
    func solvePart2() {
        var total: Int = 0
        guard let input else { return }
        for l in input.split(separator: "\n") {
            guard let n = Int(l) else { fatalError("Something is wrong.") }
            var fuel = n / 3 - 2
            while 0 < fuel {
                total += fuel
                fuel = fuel / 3 - 2
            }
        }
        answerPart2 = total
    }
    var body: some View {
        VStack {
            PuzzlePageView(url: url)
            Section {
                Button("Run part 1") { solvePart1() }
                Text(answerPart1 != nil ? "\(answerPart1!)" : "not computed yet")
                    .textSelection(.enabled)
            }
            Section {
                Button("Run part 2") { solvePart2() }
                Text(answerPart2 != nil ? "\(answerPart2!)" : "not computed yet")
                    .textSelection(.enabled)
            }
            Text("Year: \(year), Day: \(title), URL: \(url)")
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
