//
//  Day1.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/17.
//

import Foundation

struct Day1: Hashable, Identifiable, Solver {
    static func == (lhs: Day1, rhs: Day1) -> Bool {
        true
    }
    var name: String = "Day1"
    var url: String = ""
    var id = UUID()
    init() {
//            self.name = name
//            self.url = url
//            self.id = id
    }
}
