//
//  ContentView.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/16.
//

import SwiftUI


struct ContentView: View {
    private var y2019: [(any Solver, AnyView)] = [
       (Day1(), AnyView(Day1())),
       (Day2(), AnyView(Day2()))
    ]
    var body: some View {
        VStack {
            NavigationStack {
                Text("Advent of Code")
                    .font(.title)
                Section(header: Text("2019")) {
                    List(y2019, id: \.self.0.id) {puzzle in
                        NavigationLink(destination: puzzle.1) {
                            Text("--- Day \(puzzle.0.day): \(puzzle.0.title)---")
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
