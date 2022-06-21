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
    @State var input: [Int] = []
    @State var answerPart1: Int?
    @State var answerPart2: Int?
    func reset() {
        guard let path = Bundle.main.path(forResource: inputFrom, ofType: "txt") else {
            fatalError("Couldn't load \(inputFrom).txt")
        }
        do {
            input = []
            let lines = try String(contentsOfFile: path)
            for l in lines.split(separator: "\n") {
                for segment in l.split(separator: ",") {
                    guard let n = Int(segment) else { fatalError("parse errew")}
                    input.append(n)
                }
            }
        } catch {
            fatalError("Couldn't read \(inputFrom).txt")
        }
    }
    func solvePart1() {
        reset()
        answerPart1 = 0
    }
    func solvePart2() {
        reset()
        answerPart2 = 0
    }
    var body: some View {
        VStack {
            PuzzlePageView(url: url)
            Section {
                Button("Run part 1") { solvePart1() }
                Text(answerPart1 != nil ? "\(answerPart1!)" : "not computed yet")
                    .textSelection(.enabled)
                Text("loaded \(input.count) elements")
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
