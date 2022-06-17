//
//  ContentView.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/16.
//

import SwiftUI

struct ContentView: View {
    private var days: [SolverDescripter] = [
        SolverDescripter(name: "Day1")
    ]
    var body: some View {
        VStack {
            NavigationStack {
                Text("Advent of Code")
                    .font(.title)
                List(days) {
                    NavigationLink($0.name, value: $0)
                }
                .navigationDestination(for: SolverDescripter.self) { solver in
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
