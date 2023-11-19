//
//  Solver.swift
//  AdventOfCodeSwift
//
//  Created by 楢崎修二 on 2022/06/18.
//

import Foundation
import SwiftUI

protocol Solver: Identifiable, Hashable, View {
    func reset()
    var year: Int { get }
    var day: Int { get }
    var title: String { get }
    
    // func solvePart2() -> String?
    // func viewPart2() -> any View
}

extension Solver {
    var url: String {
        get {
            return "https://adventofcode.com/\(self.year)/day/\(self.day)"
        }}
    var id: UUID {
        get {
            return UUID()
        }}
    static func == (lhs: Self, rhs: Self) -> Bool {
        lhs.year == rhs.year && lhs.day == rhs.day
    }
    func hash(into hasher: inout Hasher) {
        hasher.combine(self.year)
        hasher.combine(self.day)
    }
}
