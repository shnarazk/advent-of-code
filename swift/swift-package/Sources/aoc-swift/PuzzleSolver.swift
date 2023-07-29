//
//  File.swift
//  
//
//  Created by 楢崎修二 on 2022/06/05.
//

import Foundation

protocol PuzzleSolver {
    var inputFile: String { get set }
    var delimiter: String { get set }
    func insert() -> Void
    func part1() -> Void
}
