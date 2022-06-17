//
//  Solver.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation
import SwiftUI

protocol Solver {
    func hash(into hasher: inout Hasher)
}

struct PuzzleDescripter: Hashable, Identifiable {
    var year: Int
    var day: Int
    var title: String = ""
    var url: String = ""
    var status: Int = 0
    var id: UUID = UUID()
    init(year: Int, day: Int, title: String) {
        self.year = year
        self.day = day
        self.title = title
    }
}

struct PuzzleView: View {
    @State var puzzle: PuzzleDescripter
    var body: some View {
        VStack {
            Text("Year: \(puzzle.year), Day: \(puzzle.title)")
            Text("URL: \(puzzle.url)")
                .padding(.vertical)
            Text("Description")
            Spacer()
        }
    }
}

struct PuzzleView_Previews: PreviewProvider {
    static var previews: some View {
        PuzzleView(puzzle: PuzzleDescripter(year: 2022, day: 1, title: "test"))
    }
}
