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
    @State var answerExample: Int?
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
    func solvePart1(_ example: Bool) {
        if example {
            input = [1,9,10,3,2,3,11,0,99,30,40,50]
        } else {
            reset()
            input[1] = 12
            input[2] = 2
        }
        var pc = 0
        var loop = true
        while loop {
            switch input[pc] {
            case 1:
                let op1 = input[pc + 1]
                let op2 = input[pc + 2]
                let op3 = input[pc + 3]
                input[op3] = input[op1] + input[op2]
                pc += 4
            case 2:
                let op1 = input[pc + 1]
                let op2 = input[pc + 2]
                let op3 = input[pc + 3]
                input[op3] = input[op1] * input[op2]
                pc += 4
            case 99:
                loop = false
                break
            default:
                fatalError("strange")
            }
        }
        if example {
            answerExample = input[0]
        } else {
            answerPart1 = input[0]
        }
    }
    func solvePart2() {
        reset()
        answerPart2 = 0
    }
    var body: some View {
        VStack {
            PuzzlePageView(url: url)
            Section {
                Button("check the sample") { solvePart1(true) }
                Text(answerExample != nil ? "\(answerExample!)" : "not computed yet")
            }
            Section {
                Button("Run part 1") { solvePart1(false) }
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
