//
//  Day2.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/19.
//

import Foundation
import SwiftUI

var day2 = Day2()

struct Day2: Solver, View, Identifiable, Hashable {
    var year: Int = 2019
    var day: Int = 2
    var title: String = "1202 Program Alarm"
    var inputFrom =  "input-y2019-day02"
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
            guard let n = Int(l) else { fatalError("Something is wrong.") }
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

struct Day2View_Previews: PreviewProvider {
    static var previews: some View {
        Day2()
    }
}
