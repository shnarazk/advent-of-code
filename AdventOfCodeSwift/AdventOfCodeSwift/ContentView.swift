//
//  ContentView.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/16.
//

import SwiftUI

struct Solver: Identifiable, Hashable {
    let name: String
    let id = UUID()
}

struct ContentView: View {
    private var days = [
        Solver(name: "y2019 day1")
    ]
    var body: some View {
        VStack {
            NavigationStack {
                Text("Advent of Code")
                    .font(.title)
                List(days) {
                    NavigationLink($0.name, value: $0)
                }
                .navigationDestination(for: Solver.self) { solver in
                    Text("\(solver.name)")
                }
                .navigationTitle("Result")
            }
        }
    }
}

struct ContentView_Previews: PreviewProvider {
    static var previews: some View {
        ContentView()
    }
}
