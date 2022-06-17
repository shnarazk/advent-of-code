//
//  ContentView.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/16.
//

import SwiftUI


struct ContentView: View {
    private var days: [PuzzleDescripter] = [
        day1,
        PuzzleDescripter(year: 2019, day: 1, title: "Day1"),
        PuzzleDescripter(year: 2019, day: 2, title: "Day1"),
        PuzzleDescripter(year: 2019, day: 3, title: "Day1"),
    ]
    var body: some View {
        VStack {
            NavigationStack {
                Text("Advent of Code")
                    .font(.title)
                Section(header: Text("2019")) {
                    List(days) {puzzle in
                        NavigationLink(String("\(puzzle.day), \(puzzle.title)"), value: puzzle)
                    }
                    .navigationDestination(for: PuzzleDescripter.self) { puzzle in
                        PuzzleView(puzzle: puzzle)
                    }
                    .navigationTitle("Result")
                }
                Section(header: Text("Others")) {
                    Text("None")
                }
            }
        }
    }
}

struct ContentView_Previews: PreviewProvider {
    static var previews: some View {
        ContentView()
    }
}
