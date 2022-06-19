//
//  ContentView.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/16.
//

import SwiftUI


struct ContentView: View {
    private var y2019: [PuzzleDescripter] = [
        day1,
        day2,
        PuzzleDescripter(year: 2019, day: 3, title: "Day 3", solver: nil),
        PuzzleDescripter(year: 2019, day: 4, title: "Day 4", solver: nil),
        PuzzleDescripter(year: 2019, day: 5, title: "Day 5", solver: nil),
    ]
    var body: some View {
        VStack {
            NavigationStack {
                Text("Advent of Code")
                    .font(.title)
                Section(header: Text("2019")) {
                    List(y2019) {puzzle in
                        NavigationLink(destination: PuzzleView(puzzle: puzzle)) {
                            Text("--- Day \(puzzle.day): \(puzzle.title) ---")
                        }
                    }
                    .navigationTitle("Table of Contents")
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
