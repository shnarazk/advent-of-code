//
//  Solver.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation

protocol Solver {
    func hash(into hasher: inout Hasher)
}

struct SolverDescripter: Hashable, Identifiable {
    var name: String = ""
    var url: String = ""
    var id: UUID = UUID()
    init(name: String) {
        self.name = name
    }
}
